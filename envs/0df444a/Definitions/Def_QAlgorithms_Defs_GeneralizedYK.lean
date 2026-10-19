-- Prove2me | Definitions.Def_QAlgorithms_Defs_GeneralizedYK
-- name    : QAlgorithms_Defs_GeneralizedYK
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:07.609865+00:00
-- url     : https://prove2.me/theorems/1e0886a7-6777-4745-bfb0-d143f9a017b8
-- title:
--   GeneralizedYK
-- statement:
--   GeneralizedYK
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\GeneralizedYK.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_ExactChannelCircuits
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- An isometry V : H_A tensor H_B -> H_E tensor H_D satisfies V† V = I and F(X) = Tr_E(V X V†) for every input operator X. Source: arxiv-2405.06051v6 PDF p.5; arxiv-2405.06051v6 PDF p.6; arxiv-2405.06051v6 PDF p.12. -/
def IsChosenDilation {A B E D F : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D] [NeZero F]
    (Phi : Superop (Fin A × Fin B) (Fin D))
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ)
    (layout : (Fin A × Fin B) × Fin F ≃ Fin E × Fin D)
    (U : Matrix (Fin E × Fin D) (Fin E × Fin D) ℂ) : Prop :=
  Vᴴ * V = 1 ∧ U ∈ Matrix.unitaryGroup _ ℂ ∧
    (∀ X, Phi X = traceLeft (V * X * Vᴴ)) ∧
    ∀ e d a b, V (e, d) (a, b) = U (e, d) (layout ((a, b), 0))

/-- Construct |omega>^{REDB'} by applying V to AB of |Phi>^{AR}|Phi>^{BB'}, with R identified with A and B' with B. Source: arxiv-2405.06051v6 PDF p.5; arxiv-2405.06051v6 PDF p.12. -/
def communicationState {A B E D : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D]
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ) :
    EuclideanSpace ℂ (Fin A × (Fin E × (Fin D × Fin B))) :=
  WithLp.toLp 2 fun p => V (p.2.1, p.2.2.1) (p.1, p.2.2.2) /
    ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))

/-- The map Vprep^{B' -> D'E'R'} of Eq. Source: arxiv-2405.06051v6 PDF p.10; arxiv-2405.06051v6 PDF p.11. -/
def ykPreprocessing {A B E D : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D]
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ) :
    Superop (Fin B) (Fin D × (Fin E × Fin A)) :=
  let J : Matrix (Fin D × (Fin E × Fin A)) (Fin B) ℂ :=
    Matrix.of fun p b => conj (V (p.2.1, p.1) (p.2.2, b)) / (Real.sqrt A : ℂ)
  conjSuperop J

/-- Eq. Source: arxiv-2405.06051v6 PDF p.13. -/
def ykInitialProjector {A B E D : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D]
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ) :
    Matrix (Fin D × (Fin D × (Fin E × Fin A))) (Fin D × (Fin D × (Fin E × Fin A))) ℂ :=
  let J : Matrix (Fin D × (Fin E × Fin A)) (Fin B) ℂ :=
    Matrix.of fun p b => conj (V (p.2.1, p.1) (p.2.2, b)) / (Real.sqrt A : ℂ)
  Matrix.kronecker 1 (J * Jᴴ)

/-- Eq. Source: arxiv-2405.06051v6 PDF p.13. -/
def ykSuccessProjector (A E D : ℕ) [NeZero A] [NeZero E] [NeZero D] :
    Matrix (Fin D × (Fin D × (Fin E × Fin A))) (Fin D × (Fin D × (Fin E × Fin A))) ℂ :=
  Matrix.of fun p q => if p.2.2 = q.2.2 then
    (pureDensity (finiteMaxEntangled (Fin D))) (p.1, p.2.1) (q.1, q.2.1) else 0

/-- Eq. Source: arxiv-2405.06051v6 PDF p.13. -/
def projectorPhaseRotation {I : Type} [Fintype I] [DecidableEq I]
    (Pi : Matrix I I ℂ) (theta : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((Complex.I * (theta : ℂ)) • (2 • Pi - 1))

/-- Eq. Source: arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.13; arxiv-2405.06051v6 PDF p.25. -/
def ykPhaseSequence {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    (Pi1 Pi2 : Matrix I I ℂ) (phi : Fin t → ℝ) : Matrix I I ℂ :=
  orderedProd fun j : Fin t => projectorPhaseRotation
    (if (j : ℕ) % 2 = 0 then Pi2 else Pi1) (phi j)

/-- Eq. Source: arxiv-2405.06051v6 PDF p.9; arxiv-2405.06051v6 PDF p.13. -/
def ykRealQsvt {I : Type} [Fintype I] [DecidableEq I] {t : ℕ}
    (Pi1 Pi2 : Matrix I I ℂ) (phi : Fin t → ℝ) : Matrix (I × Bool) (I × Bool) ℂ :=
  Matrix.kronecker (ykPhaseSequence Pi1 Pi2 phi) (pureDensity (act hadamard (ket false))) +
    Matrix.kronecker (ykPhaseSequence Pi1 Pi2 (fun j => -phi j)) (pureDensity (act hadamard (ket true)))

/-- Eq. Source: arxiv-2405.06051v6 PDF p.11; arxiv-2405.06051v6 PDF p.12; arxiv-2405.06051v6 PDF p.13. -/
def ykDecoder {A B E D t : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D]
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ) (phi : Fin t → ℝ) :
    Superop (Fin D × Fin B) (Fin A) :=
  fun X =>
    let Y := idTensorSuperop (R := Fin D) (ykPreprocessing V) X
    let G := ykRealQsvt (ykInitialProjector V) (ykSuccessProjector A E D) phi
    let Z := conjSuperop G (Matrix.kronecker Y (pureDensity (ket false)))
    Matrix.of fun a b => ∑ d : Fin D, ∑ dp : Fin D, ∑ e : Fin E, ∑ h : Bool,
      Z ((d, (dp, (e, a))), h) ((d, (dp, (e, b))), h)

/-- Eq. Source: arxiv-2405.06051v6 PDF p.5. -/
def recoveryError {A B E D : ℕ} [NeZero A] [NeZero B] [NeZero E] [NeZero D]
    (V : Matrix (Fin E × Fin D) (Fin A × Fin B) ℂ)
    (Dec : Superop (Fin D × Fin B) (Fin A)) : ℝ :=
  let omega := pureDensity (communicationState V)
  let reduced : Matrix (Fin A × (Fin D × Fin B)) (Fin A × (Fin D × Fin B)) ℂ :=
    Matrix.of fun p q => ∑ e : Fin E, omega (p.1, (e, p.2)) (q.1, (e, q.2))
  2⁻¹ * traceNorm (pureDensity (finiteMaxEntangled (Fin A)) - idTensorSuperop Dec reduced)

/-- Sanity test. Source: arxiv-2405.06051v6 PDF p.5; arxiv-2405.06051v6 PDF p.6; arxiv-2405.06051v6 PDF p.12. -/
example {I : Type} [Fintype I] [DecidableEq I] (Pi : Matrix I I ℂ) :
    projectorPhaseRotation Pi 0 = 1 := by simp [projectorPhaseRotation]

/-- Sanity test. Source: arxiv-2405.06051v6 PDF p.5; arxiv-2405.06051v6 PDF p.6; arxiv-2405.06051v6 PDF p.12. -/
example {I : Type} [Fintype I] [DecidableEq I] (P Q : Matrix I I ℂ) (phi : Fin 3 → ℝ) :
    ykPhaseSequence P Q phi =
      projectorPhaseRotation Q (phi 2) * projectorPhaseRotation P (phi 1) *
        projectorPhaseRotation Q (phi 0) := by
  simp [ykPhaseSequence, orderedProd, List.ofFn_succ, Matrix.mul_assoc]

end QAlgorithms


