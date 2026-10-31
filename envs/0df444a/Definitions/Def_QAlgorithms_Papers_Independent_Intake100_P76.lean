-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76
-- name    : QAlgorithms_Papers_Independent_Intake100_P76
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T18:19:07.869548+00:00
-- url     : https://prove2.me/theorems/21286540-b0cd-4cc6-b6e9-1a51fdb590b3
-- title:
--   Definitions for Separability and entanglement of composite quantum systems
-- statement:
--   The objects the formalized statements of *Separability and entanglement of composite quantum systems* (arXiv:quant-ph/9707043) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsUnitProduct`: PDF p.1, Eq. (2): a normalized product vector, with subsystem A first.
--   - `InProductCone`: PDF p.2, Eq. (5): finite nonnegative sums of the projectors specified by V. Zero is permitted, including when V is empty. No closedness of V is imposed.
--   - `IsBSAOver`: PDF p.2, Theorem 1: an attained trace maximum over a prescribed V. Theorems supply that V consists of normalized product vectors in range(rho). This predicate does not assert that a maximizer exists for every V.
--   - `IsBSA`: PDF pp.2–3: the unrestricted best separable approximation. The accepted separable positive cone is unnormalized and includes zero.
--   - `MaximalSingle`: PDF p.2, Definition 1 and its proof: maximal nonnegative subtraction. Printed “epsilon >= 0” and “not positive definite” are read as “epsilon > 0” and failure of positive semidefiniteness, as explicitly used in the proof.
--   - `MaximalPair`: PDF p.2, Definition 2: both individual coefficients are maximal and their sum is globally maximal among all feasible nonnegative pairs. This is the definition, independently of the incorrect printed formulas of Lemma 2.
--   - `bsaRepresentative`: PDF pp.2–3: select an unrestricted optimizer if one exists, otherwise zero. Existence on density matrices is a theorem below, not an assumption of this definition.
--   - `bsaWeight`: PDF p.3, Eq. (11): the optimal separable weight is the optimizer's trace.
--   - `bsaEntanglement`: PDF p.3, Eqs. (12)–(13): the authors' two-qubit BSA entanglement functional in ebits. The normalized residual is used, not the original mixed density matrix. A zero residual has value zero; the fallback off the density-matrix domain has no claimed physical meaning. The accepted vnEntropy uses base-two logarithms.
--   - `wernerDensity`: PDF p.3, Eq. (14): the Werner density matrix (1-x) I_4/4 + x |Psi-><Psi-|. The source's parameter domain for all claims is 0 < x < 1.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, https://arxiv.org/abs/quant-ph/9707043v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

/-!
Statements from Lewenstein–Sanpera, arXiv:quant-ph/9707043v1, PDF pp.1–4.
Only unrestricted BSA existence is asserted. The prescribed-set existence,
printed pair formulas, pairwise certificate and literal endpoint uniqueness
are deferred in the accompanying HARD.md. All new definitions are paper-local;
the support inverse and singlet projector are reused from pinned accepted modules.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.1, Eq. (2): a normalized product vector, with subsystem A first. -/
def IsUnitProduct (v : EuclideanSpace ℂ (A × B)) : Prop :=
  ∃ e : EuclideanSpace ℂ A, ∃ f : EuclideanSpace ℂ B,
    IsState e ∧ IsState f ∧ v = tensorVec e f

/-- PDF p.2, Eq. (5): finite nonnegative sums of the projectors specified by V.
Zero is permitted, including when V is empty. No closedness of V is imposed. -/
def InProductCone (V : Set (EuclideanSpace ℂ (A × B)))
    (S : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ m : ℕ, ∃ w : Fin m → ℝ, ∃ v : Fin m → EuclideanSpace ℂ (A × B),
    (∀ k, 0 ≤ w k) ∧ (∀ k, v k ∈ V) ∧
    S = ∑ k, (w k : ℂ) • pureDensity (v k)

/-- PDF p.2, Theorem 1: an attained trace maximum over a prescribed V.
Theorems supply that V consists of normalized product vectors in range(rho).
This predicate does not assert that a maximizer exists for every V. -/
def IsBSAOver (rho : Matrix (A × B) (A × B) ℂ)
    (V : Set (EuclideanSpace ℂ (A × B))) (S : Matrix (A × B) (A × B) ℂ) : Prop :=
  InProductCone V S ∧ (rho - S).PosSemidef ∧
    ∀ T, InProductCone V T → (rho - T).PosSemidef → T.trace.re ≤ S.trace.re

/-- PDF pp.2–3: the unrestricted best separable approximation. The accepted
separable positive cone is unnormalized and includes zero. -/
def IsBSA (rho S : Matrix (A × B) (A × B) ℂ) : Prop :=
  IsSeparablePositive S ∧ (rho - S).PosSemidef ∧
    ∀ T, IsSeparablePositive T → (rho - T).PosSemidef → T.trace.re ≤ S.trace.re

/-- PDF p.2, Definition 1 and its proof: maximal nonnegative subtraction.
Printed “epsilon >= 0” and “not positive definite” are read as “epsilon > 0”
and failure of positive semidefiniteness, as explicitly used in the proof. -/
def MaximalSingle (rho : Matrix I I ℂ) (psi : EuclideanSpace ℂ I)
    (lambda : ℝ) : Prop :=
  0 ≤ lambda ∧ (rho - (lambda : ℂ) • pureDensity psi).PosSemidef ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ¬ (rho - ((lambda + epsilon : ℝ) : ℂ) • pureDensity psi).PosSemidef

/-- PDF p.2, Definition 2: both individual coefficients are maximal and their
sum is globally maximal among all feasible nonnegative pairs. This is the
definition, independently of the incorrect printed formulas of Lemma 2. -/
def MaximalPair (rho : Matrix I I ℂ) (psi phi : EuclideanSpace ℂ I)
    (lambda mu : ℝ) : Prop :=
  0 ≤ lambda ∧ 0 ≤ mu ∧
    (rho - (lambda : ℂ) • pureDensity psi - (mu : ℂ) • pureDensity phi).PosSemidef ∧
    MaximalSingle (rho - (mu : ℂ) • pureDensity phi) psi lambda ∧
    MaximalSingle (rho - (lambda : ℂ) • pureDensity psi) phi mu ∧
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (rho - (a : ℂ) • pureDensity psi - (b : ℂ) • pureDensity phi).PosSemidef →
        a + b ≤ lambda + mu

/-- PDF pp.2–3: select an unrestricted optimizer if one exists, otherwise zero.
Existence on density matrices is a theorem below, not an assumption of this definition. -/
def bsaRepresentative (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ := by
  classical
  exact if h : ∃ S, IsBSA rho S then Classical.choose h else 0

/-- PDF p.3, Eq. (11): the optimal separable weight is the optimizer's trace. -/
def bsaWeight (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  (bsaRepresentative rho).trace.re

/-- PDF p.3, Eqs. (12)–(13): the authors' two-qubit BSA entanglement functional
in ebits. The normalized residual is used, not the original mixed density matrix.
A zero residual has value zero; the fallback off the density-matrix domain has
no claimed physical meaning. The accepted vnEntropy uses base-two logarithms. -/
def bsaEntanglement (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  let R := rho - bsaRepresentative rho
  let w := R.trace.re
  if w = 0 then 0 else w * vnEntropy (traceRight ((w : ℂ)⁻¹ • R))

/-- PDF p.3, Eq. (14): the Werner density matrix (1-x) I_4/4 + x |Psi-><Psi-|.
The source's parameter domain for all claims is 0 < x < 1. -/
def wernerDensity (x : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (((1 - x) / 4 : ℝ) : ℂ) • 1 + (x : ℂ) • QAlgorithms.Papers.Independent.Dependency50.P06.singlet

/-- Normalized local states give precisely a unit product vector (PDF p.1). -/
example (e : EuclideanSpace ℂ A) (f : EuclideanSpace ℂ B)
    (he : IsState e) (hf : IsState f) : IsUnitProduct (tensorVec e f) :=
  ⟨e, f, he, hf, rfl⟩

/-- The empty generating family still permits the zero separable operator. -/
example : InProductCone (∅ : Set (EuclideanSpace ℂ (A × B))) 0 := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro k; exact Fin.elim0 k
  · intro k; exact Fin.elim0 k
  · simp

/-- A restricted optimizer carries the PSD residual required by the source. -/
example (rho S : Matrix (A × B) (A × B) ℂ) (V : Set (EuclideanSpace ℂ (A × B)))
    (h : IsBSAOver rho V S) : (rho - S).PosSemidef := h.2.1

/-- A global optimizer carries the PSD residual required by the source. -/
example (rho S : Matrix (A × B) (A × B) ℂ) (h : IsBSA rho S) :
    (rho - S).PosSemidef := h.2.1

/-- A maximal subtraction coefficient cannot be negative. -/
example (rho : Matrix I I ℂ) (psi : EuclideanSpace ℂ I) (l : ℝ)
    (h : MaximalSingle rho psi l) : 0 ≤ l := h.1

/-- Definition 2 includes a bound against the feasible zero pair. -/
example (rho : Matrix I I ℂ) (psi phi : EuclideanSpace ℂ I) (l m : ℝ)
    (h : MaximalPair rho psi phi l m) : 0 ≤ l + m := add_nonneg h.1 h.2.1

/-- The representative's fallback is zero only when no optimizer exists. -/
example (rho : Matrix (A × B) (A × B) ℂ) (h : ¬ ∃ S, IsBSA rho S) :
    bsaRepresentative rho = 0 := by
  classical
  simp [bsaRepresentative, h]

/-- The scalar weight is defined from the chosen operator, not independently. -/
example (rho : Matrix (A × B) (A × B) ℂ) :
    bsaWeight rho = (bsaRepresentative rho).trace.re := rfl

/-- At a vanishing residual the functional is explicitly zero. -/
example (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : rho - bsaRepresentative rho = 0) : bsaEntanglement rho = 0 := by
  simp [bsaEntanglement, h]

/-- The imported singlet projector has zero |00> population, pinning the basis. -/
example : QAlgorithms.Papers.Independent.Dependency50.P06.singlet (0, 0) (0, 0) = 0 := by
  simp [QAlgorithms.Papers.Independent.Dependency50.P06.singlet]

/-- The x=0 extension of Eq. (14) is I_4/4; source theorems keep 0<x<1. -/
example : wernerDensity 0 = (1 / 4 : ℂ) • 1 := by
  simp [wernerDensity]

end QAlgorithms.Papers.Independent.Intake100.P76


