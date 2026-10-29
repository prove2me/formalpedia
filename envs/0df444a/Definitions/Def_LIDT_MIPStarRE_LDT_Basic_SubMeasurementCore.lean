-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
-- name    : LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:50:03.698745+00:00
-- url     : https://prove2.me/theorems/ea1ab487-32af-45ab-8545-d11bb01e1c82
-- title:
--   LIDT definitions: LDT / Basic / SubMeasurementCore
-- statement:
--   This bundle defines the paper-local measurement structures used throughout the LDT formalization. It distinguishes submeasurements, complete measurements, projective variants, trivial distinguished-outcome constructions, one-outcome submeasurements, and the promotion of a complete submeasurement to a measurement.
--
--   Principal definitions:
--   - `SubMeas`: a positive operator-valued submeasurement with a finite outcome type.
--   - `Measurement`: a complete POVM whose effects sum to identity.
--   - `ProjSubMeas`: a submeasurement with projective effects.
--   - `ProjMeas`: a complete projective measurement.
--   - `SubMeas.toMeasurement`: promotes a complete submeasurement to a measurement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/SubMeasurementCore.lean#L17-L439

-- Generated from MIPStarRE/LDT/Basic/SubMeasurementCore.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open scoped _root_.Matrix

namespace LIDT

/-!
# Core submeasurement structures for the low individual degree test

Foundational measurement, submeasurement, and projective-measurement structures.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A paper-local submeasurement with outcomes in `α` and Hilbert space index `ι`.

There is intentionally no global `Inhabited` instance: the zero family satisfies
these raw axioms, but using it as an ambient default would silently turn later
arguments into vacuous submeasurement statements. -/
structure SubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  outcome : α → MIPStarRE.Quantum.Op ι := fun _ => 0
  total : MIPStarRE.Quantum.Op ι := 0
  outcome_pos : ∀ a, 0 ≤ outcome a
  sum_eq_total : ∑ a, outcome a = total
  total_le_one : total ≤ 1

/-- A paper-local measurement: a POVM whose PSD effects sum to the identity. -/
structure Measurement (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  total_eq_one : total = 1

set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- For a trivial distinguished-outcome measurement, every outcome operator is
positive semidefinite: `0 ≤ if a = a₀ then 1 else 0`. -/
private theorem Measurement.trivialDistinguishedOutcome_outcome_pos
    {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] (a₀ a : α) :
    (0 : MIPStarRE.Quantum.Op ι) ≤ if a = a₀ then 1 else 0 := by
  by_cases h : a = a₀ <;> simp [h]

open scoped Classical in
/-- ⚠️ DEGENERATE — Construct a trivial measurement where only the distinguished
outcome `a₀` is the identity and all other outcomes are zero.

This is a valid POVM but highly degenerate: it is only used in vacuous
fallback branches of the proof where the error bound is ≥ 1 (see
`Test/MainTheorem.lean:mainFormal_trivial_witness`).

Call this function explicitly with a chosen outcome.  There is intentionally no
ambient `Inhabited (Measurement α ι)` instance: choosing a hidden
`default : α` would make degenerate witnesses available to paper-facing
existential statements without displaying the selected outcome. -/
noncomputable def Measurement.trivialDistinguishedOutcome
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (a₀ : α) : Measurement α ι where
  toSubMeas := {
    outcome := fun a => if a = a₀ then 1 else 0
    total := 1
    outcome_pos := fun a => by
      exact Measurement.trivialDistinguishedOutcome_outcome_pos a₀ a
    sum_eq_total :=
      (Finset.sum_ite_eq' Finset.univ a₀ fun _ => 1).trans (if_pos (Finset.mem_univ a₀))
    total_le_one := le_rfl
  }
  total_eq_one := rfl

/-- A paper-local projective submeasurement (each effect is idempotent).

There is intentionally no global `Inhabited` instance: any such default would
again collapse to the degenerate zero family. -/
structure ProjSubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- A paper-local projective measurement (complete POVM + projective). -/
structure ProjMeas (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends Measurement α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- For a trivial distinguished-outcome projective measurement, every outcome operator
is idempotent. -/
private theorem ProjMeas.trivialDistinguishedOutcome_proj
    {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (a₀ a : α) :
    (Measurement.trivialDistinguishedOutcome (ι := ι) a₀).outcome a *
        (Measurement.trivialDistinguishedOutcome (ι := ι) a₀).outcome a =
      (Measurement.trivialDistinguishedOutcome (ι := ι) a₀).outcome a := by
  classical
  by_cases h : a = a₀ <;> simp [Measurement.trivialDistinguishedOutcome, h]

/-- ⚠️ DEGENERATE — Construct a trivial projective measurement where only the
distinguished outcome `a₀` is the identity and all other outcomes are zero.

This is a valid projective POVM but highly degenerate: see the discussion at
`Measurement.trivialDistinguishedOutcome`.  Prefer calling this function
explicitly (with a chosen outcome) rather than relying on the ambient
`Inhabited` instance.  As for `Measurement`, there is intentionally no ambient
`Inhabited (ProjMeas α ι)` instance. -/
noncomputable def ProjMeas.trivialDistinguishedOutcome
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (a₀ : α) : ProjMeas α ι where
  toMeasurement := Measurement.trivialDistinguishedOutcome a₀
  proj := fun a => by
    exact ProjMeas.trivialDistinguishedOutcome_proj a₀ a

/-! ### Derived properties -/

/-- Two submeasurements are equal when they have the same outcome operators and
the same total operator. -/
@[ext] theorem SubMeas.ext {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    {A B : SubMeas α ι}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a)
    (htotal : A.total = B.total) :
    A = B := by
  cases A with
  | mk outcomeA totalA posA sumA leA =>
      cases B with
      | mk outcomeB totalB posB sumB leB =>
          have houtcome' : outcomeA = outcomeB := by
            funext a
            exact houtcome a
          cases houtcome'
          cases htotal
          cases Subsingleton.elim posB posA
          cases Subsingleton.elim sumB sumA
          cases Subsingleton.elim leB leA
          rfl

/-- Two measurements are equal when they have the same outcome operators. -/
@[ext] theorem Measurement.ext {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    {A B : Measurement α ι}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a) :
    A = B := by
  cases A with
  | mk AtoSubMeas AtotalEqOne =>
      cases B with
      | mk BtoSubMeas BtotalEqOne =>
          have hsub : AtoSubMeas = BtoSubMeas := by
            apply SubMeas.ext
            · intro a
              simpa using houtcome a
            · calc
                AtoSubMeas.total = 1 := AtotalEqOne
                _ = BtoSubMeas.total := BtotalEqOne.symm
          cases hsub
          cases Subsingleton.elim BtotalEqOne AtotalEqOne
          rfl

/-- Two projective measurements are equal when they have the same outcome
operators. -/
@[ext] theorem ProjMeas.ext {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    {A B : ProjMeas α ι}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a) :
    A = B := by
  cases A with
  | mk AtoMeasurement Aproj =>
      cases B with
      | mk BtoMeasurement Bproj =>
          have hmeas : AtoMeasurement = BtoMeasurement := by
            apply Measurement.ext
            intro a
            simpa using houtcome a
          cases hmeas
          cases Subsingleton.elim Bproj Aproj
          rfl

/-- A one-outcome submeasurement associated to a single positive operator
bounded by the identity. -/
def SubMeas.singleOutcome {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Op ι) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    SubMeas Unit ι where
  outcome := fun _ => A
  total := A
  outcome_pos := fun _ => hA_pos
  sum_eq_total := Fintype.sum_unique fun _ => A
  total_le_one := hA_le_one

@[simp] theorem SubMeas.singleOutcome_outcome {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Op ι) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1)
    (u : Unit) :
    (SubMeas.singleOutcome (ι := ι) A hA_pos hA_le_one).outcome u = A :=
  rfl

@[simp] theorem SubMeas.singleOutcome_total {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Op ι) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    (SubMeas.singleOutcome (ι := ι) A hA_pos hA_le_one).total = A :=
  rfl

/-- PSD outcomes are Hermitian. -/
theorem SubMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (a : α) :
    (A.outcome a)ᴴ = A.outcome a :=
  (Matrix.nonneg_iff_posSemidef.mp (A.outcome_pos a)).isHermitian.eq

/-- PSD outcomes are Hermitian. -/
theorem Measurement.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (a : α) :
    (M.outcome a)ᴴ = M.outcome a :=
  SubMeas.outcome_hermitian M.toSubMeas a

/-- Each POVM element is bounded by the identity: `outcome a ≤ 1`.
Proof: `outcome a = 1 - ∑_{b ≠ a} outcome b ≤ 1` since all terms are PSD. -/
theorem Measurement.outcome_le_one {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (a : α) :
    M.outcome a ≤ 1 := by
  calc M.outcome a
      ≤ ∑ i : α, M.outcome i :=
        Finset.single_le_sum (fun i _ => M.outcome_pos i) (Finset.mem_univ a)
    _ = 1 := by
        rw [M.sum_eq_total, M.total_eq_one]

/-- The outcome operators of a measurement sum to the identity. -/
theorem Measurement.sum_eq {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) :
    ∑ a, M.outcome a = 1 := by
  rw [M.sum_eq_total, M.total_eq_one]



/-- Promote a complete submeasurement to a measurement.

This is the explicit bridge from the paper's sub-measurement convention
`∑ a, A_a ≤ I` to the POVM convention `∑ a, A_a = I`: callers must supply the
completion proof rather than relying on a degenerate default. -/
def SubMeas.toMeasurement {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) :
    Measurement α ι where
  toSubMeas := A
  total_eq_one := hcomplete

@[simp] theorem SubMeas.toMeasurement_toSubMeas {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) :
    (A.toMeasurement hcomplete).toSubMeas = A :=
  rfl

@[simp] theorem SubMeas.toMeasurement_outcome {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) (a : α) :
    (A.toMeasurement hcomplete).outcome a = A.outcome a :=
  rfl

/-- Every submeasurement outcome is bounded by the total operator. -/
theorem SubMeas.outcome_le_total {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (a : α) :
    A.outcome a ≤ A.total := by
  calc A.outcome a
      ≤ ∑ i : α, A.outcome i :=
        Finset.single_le_sum (fun i _ => A.outcome_pos i) (Finset.mem_univ a)
    _ = A.total := A.sum_eq_total

/-- Every submeasurement outcome is bounded by the identity. -/
theorem SubMeas.outcome_le_one {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (a : α) :
    A.outcome a ≤ 1 :=
  le_trans (A.outcome_le_total a) A.total_le_one

/-- The total operator of a submeasurement is PSD. -/
theorem SubMeas.total_nonneg {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : 0 ≤ A.total := by
  rw [← A.sum_eq_total]
  exact Finset.sum_nonneg fun a _ => A.outcome_pos a

/-- Projective submeasurement outcomes are Hermitian (PSD from idempotence). -/
theorem ProjSubMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a :=
  SubMeas.outcome_hermitian P.toSubMeas a

/-- Each projective outcome is absorbed by the total operator. -/
theorem ProjSubMeas.outcome_mul_total_eq_outcome {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (a : α) :
    P.outcome a * P.total = P.outcome a := by
  let Pa := P.outcome a
  let R : MIPStarRE.Quantum.Op ι := 1 - P.total
  have hPa_herm : Paᴴ = Pa := by
    simpa [Pa] using P.outcome_hermitian a
  have hPa_star : IsStarProjection Pa :=
    isStarProjection_iff'.2 ⟨by simpa [Pa] using P.proj a, hPa_herm⟩
  have hR_nonneg : 0 ≤ R := by
    simpa [R] using sub_nonneg.mpr P.total_le_one
  have hR_le_self : R ≤ 1 - Pa := by
    simpa [R, Pa] using
      sub_le_sub_left (P.outcome_le_total a) (1 : MIPStarRE.Quantum.Op ι)
  have hPaRPa_nonneg : 0 ≤ Pa * R * Pa := by
    exact IsSelfAdjoint.conjugate_nonneg hR_nonneg hPa_herm
  have hPa_one_sub_Pa : Pa * (1 - Pa) * Pa = 0 := by
    rw [hPa_star.mul_one_sub_self, zero_mul]
  have hPaRPa_eq_zero : Pa * R * Pa = 0 := by
    apply le_antisymm
    · calc
        Pa * R * Pa ≤ Pa * (1 - Pa) * Pa := by
          exact IsSelfAdjoint.conjugate_le_conjugate hR_le_self hPa_herm
        _ = 0 := hPa_one_sub_Pa
    · simpa using hPaRPa_nonneg
  have hP_total_herm : P.totalᴴ = P.total := by
    exact (Matrix.nonneg_iff_posSemidef.mp P.total_nonneg).isHermitian.eq
  have hR_herm : Rᴴ = R := by
    simp [R, hP_total_herm]
  have hR_sq_le : R * R ≤ R := by
    have hR_le_one : R ≤ 1 := by
      simpa [R] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) P.total_nonneg
    exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
  have hRPa_conj_mul : (R * Pa)ᴴ * (R * Pa) = Pa * (R * R) * Pa := by
    calc
      (R * Pa)ᴴ * (R * Pa) = (Paᴴ * Rᴴ) * (R * Pa) := by
        simp [Matrix.conjTranspose_mul]
      _ = Pa * (R * R) * Pa := by simp [hPa_herm, hR_herm, mul_assoc]
  have hRPa_eq_zero : R * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hRPa_conj_mul]
    apply le_antisymm
    · calc
        Pa * (R * R) * Pa ≤ Pa * R * Pa := by
          exact IsSelfAdjoint.conjugate_le_conjugate hR_sq_le hPa_herm
        _ = 0 := hPaRPa_eq_zero
    · have hnonneg : 0 ≤ Pa * (R * R) * Pa := by
        exact IsSelfAdjoint.conjugate_nonneg
          (show 0 ≤ R * R by
            exact Commute.mul_nonneg hR_nonneg hR_nonneg (Commute.refl R))
          hPa_herm
      simpa using hnonneg
  calc
    P.outcome a * P.total = Pa * (1 - R) := by
      simp [Pa, R, sub_eq_add_neg, add_comm, add_left_comm]
    _ = Pa - Pa * R := by rw [mul_sub, mul_one]
    _ = Pa := by
          have : Pa * R = 0 := by
            simpa [hPa_herm, hR_herm] using congrArg Matrix.conjTranspose hRPa_eq_zero
          simp [this]
    _ = P.outcome a := by rfl

/-- The total operator of a projective submeasurement is itself a projector. -/
theorem ProjSubMeas.total_proj {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) :
    P.total * P.total = P.total := by
  calc
    P.total * P.total = (∑ a : α, P.outcome a) * P.total := by rw [P.sum_eq_total]
    _ = ∑ a : α, P.outcome a * P.total := by rw [Matrix.sum_mul]
    _ = ∑ a : α, P.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact P.outcome_mul_total_eq_outcome a
    _ = P.total := P.sum_eq_total

/-- Distinct outcomes of a projective submeasurement are orthogonal. -/
theorem ProjSubMeas.outcome_orthogonal {α : Type*}
    {ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (P : ProjSubMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  classical
  set Pa := P.outcome a
  set Pb := P.outcome b
  have hsum : Pa + Pb ≤ P.total := by
    calc
      Pa + Pb
        = ∑ i ∈ ({a, b} : Finset α), P.outcome i := by
            simp [Pa, Pb, hab]
      _ ≤ ∑ i : α, P.outcome i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by simp)
              (fun i _ _ => P.outcome_pos i)
      _ = P.total := P.sum_eq_total
  have hPb_le : Pb ≤ 1 - Pa := by
    calc
      Pb = Pa + Pb - Pa := by abel
      _ ≤ P.total - Pa := by
          exact sub_le_sub_right hsum Pa
      _ ≤ 1 - Pa := by
          exact sub_le_sub_right P.total_le_one Pa
  have hPa_herm : Paᴴ = Pa := P.outcome_hermitian a
  have hPb_herm : Pbᴴ = Pb := P.outcome_hermitian b
  have hPa_star : IsStarProjection Pa :=
    isStarProjection_iff'.2 ⟨by simpa [Pa] using P.proj a, hPa_herm⟩
  have hPaPbPa_nonneg : 0 ≤ Pa * Pb * Pa :=
    IsSelfAdjoint.conjugate_nonneg (P.outcome_pos b) hPa_herm
  have hPa_idem : Pa * (1 - Pa) * Pa = 0 := by
    rw [hPa_star.mul_one_sub_self, zero_mul]
  have hPaPbPa_eq_zero : Pa * Pb * Pa = 0 := by
    apply le_antisymm
    · calc
        Pa * Pb * Pa ≤ Pa * (1 - Pa) * Pa :=
          IsSelfAdjoint.conjugate_le_conjugate hPb_le hPa_herm
        _ = 0 := hPa_idem
    · exact hPaPbPa_nonneg
  have hPbPa_eq_zero : Pb * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      (Pb * Pa)ᴴ * (Pb * Pa) = (Paᴴ * Pbᴴ) * (Pb * Pa) := by
        simp [Matrix.conjTranspose_mul]
      _ = Pa * (Pb * Pb) * Pa := by
        simp [hPa_herm, hPb_herm, mul_assoc]
      _ = Pa * Pb * Pa := by simp [Pb, P.proj b]
      _ = 0 := hPaPbPa_eq_zero
  calc
    Pa * Pb = (Pb * Pa)ᴴ := by
      simp [Matrix.conjTranspose_mul, hPa_herm, hPb_herm]
    _ = 0 := by rw [hPbPa_eq_zero]; simp

/-- Projective measurement outcomes are Hermitian (inherited from Measurement.outcome_pos). -/
theorem ProjMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a :=
  Measurement.outcome_hermitian P.toMeasurement a

/-- Distinct outcomes of a projective measurement are orthogonal. -/
theorem ProjMeas.outcome_orthogonal {α : Type*}
    {ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (P : ProjMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  let P' : ProjSubMeas α ι :=
    { toSubMeas := P.toSubMeas
      proj := P.proj }
  simpa [P'] using P'.outcome_orthogonal a b hab




end MIPStarRE.LDT

end

end LIDT


