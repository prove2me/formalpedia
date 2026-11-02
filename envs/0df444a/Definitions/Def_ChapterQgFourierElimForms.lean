-- Prove2me | Definitions.Def_ChapterQgFourierElimForms
-- name    : ChapterQgFourierElimForms
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-01T18:09:50.148025+00:00
-- url     : https://prove2.me/theorems/34a8147f-17f4-47db-818f-45bb102a36b8
-- title:
--   Chapter QgFourierElim Forms
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgFourierElimination.lean`): the form/field-value layer (FormIdx, torsion/dGauge/gauge3d forms, ind, gCoef, mAbs, formValue, gGram) carved out of ChapterQgFourierElimination under the §2.13 new-name route, since submit-definition cannot update an existing name. See BookProof/ChapterQgFourierElimination.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgFourierElimination.lean

-- Generated from ChapterQgFourierElimination.lean — the form/field-value layer
-- that the platform's served ChapterQgFourierElimination copy predates
-- (§2.13 new-name route: submit-definition rejects an existing name, so the
-- decls the Session-28 port added live here instead).
import Definitions.Def_ChapterQgFourierElimination
import Definitions.Def_ChapterQgBrstDerivativeGauge
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Mathlib

/-!
# The linear forms of the gauge-fixed QG Hamiltonian (form/field-value layer)

`ChapterQgFourierElimination` as served by the platform predates the
Session-28 port: it carries only the elimination core (`Comp`, `dIdx`,
`eIdx`, `elimConfig`, `elimConfig_e/d`, `elimD`, `elimTorsion`, `elimGram`,
`qgElimModes`).  The form layer built on top of it — `FormIdx`, the
torsion/derivative-gauge/3D-gauge forms, `ind`, `gCoef` and its evaluation
lemmas, the momentum bound `mAbs`, `formValue` and its three rewrite lemmas,
and `gGram` — is published here as a separate bundle, because
`submit-definition` cannot update an existing name (§2.13).

Nothing is assumed: no `axiom`, no `sorry`.
-/

open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

namespace BookProof.QgFourierElim

/-- The linear forms of the gauge-fixed gravity Hamiltonian: the twenty-seven torsion forms,
the twenty-seven forms of the derivative-variable gauge fixing, and the three forms of the
3D (transverse) gauge fixing. -/
abbrev FormIdx := (Fin 3 × Fin 3 × Fin 3) ⊕ ((Fin 3 × Fin 3 × Fin 3) ⊕ Fin 3)

/-- The torsion form `T_{μν}^i`. -/
def torsionF (mu nu i : Fin 3) : FormIdx := Sum.inl (mu, nu, i)

/-- The gauge-fixing form `G_{μν}^i = D_{μν}^i − i k_μ e_ν^i` of the derivative variable
`D_{μν}^i`. -/
def dGaugeF (mu nu i : Fin 3) : FormIdx := Sum.inr (Sum.inl (mu, nu, i))

/-- The 3D gauge-fixing (transverse) form `C^i = Σ_μ i k_μ e_μ^i`. -/
def gauge3dF (i : Fin 3) : FormIdx := Sum.inr (Sum.inr i)


/- Inlined from `BookProof/ChapterQgVielbeinScalaronGaugeFL/Part1.lean`: that chapter
   has no bundle of its own (its namespace `BookProof.QgVielbeinScalaronGaugeFL` resolves
   nowhere), so the pre-elimination half of the model travels with the bundles that inline
   its content.  This bundle is where `BookProof.QgFourierElim` lives, and the theorem
   stubs `formValue_*_elimConfig` resolve `formValue` here. -/

/-- A mode of the extended (vielbein + derivative variables) field space: a momentum in
`ℤ³` together with a component.  There are infinitely many — no lattice, no truncation. -/
abbrev GMode := Mom × Comp

theorem card_formIdx : Fintype.card FormIdx = 57 := by decide

/-- The indicator of a component. -/
def ind (c d : Comp) : ℂ := if c = d then 1 else 0

theorem norm_ind_le (c d : Comp) : ‖ind c d‖ ≤ 1 := by
  simp only [ind]; split <;> simp

theorem sum_ind_mul (d : Comp) (z : Comp → ℂ) : ∑ c : Comp, ind c d * z c = z d := by
  classical
  rw [Finset.sum_eq_single d]
  · simp [ind]
  · intro c _ hc
    simp [ind, hc]
  · intro h
    exact absurd (Finset.mem_univ d) h

/-- **The coefficient vectors of the three families of linear forms** at momentum `k`. -/
def gCoef (k : Mom) : FormIdx → Comp → ℂ
  | Sum.inl (mu, nu, i), c => ind c (dIdx mu nu i) - ind c (dIdx nu mu i)
  | Sum.inr (Sum.inl (mu, nu, i)), c =>
      ind c (dIdx mu nu i) - Complex.I * ((k mu : ℤ) : ℂ) * ind c (eIdx nu i)
  | Sum.inr (Sum.inr i), c => ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * ind c (eIdx mu i)

@[simp] theorem gCoef_torsion (k : Mom) (mu nu i : Fin 3) (c : Comp) :
    gCoef k (torsionF mu nu i) c = ind c (dIdx mu nu i) - ind c (dIdx nu mu i) := rfl

@[simp] theorem gCoef_dGauge (k : Mom) (mu nu i : Fin 3) (c : Comp) :
    gCoef k (dGaugeF mu nu i) c
      = ind c (dIdx mu nu i) - Complex.I * ((k mu : ℤ) : ℂ) * ind c (eIdx nu i) := rfl

@[simp] theorem gCoef_gauge3d (k : Mom) (i : Fin 3) (c : Comp) :
    gCoef k (gauge3dF i) c = ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * ind c (eIdx mu i) :=
  rfl

/-! ### The size of the momentum -/

/-- `|k|`. -/
def mAbs (k : Mom) : ℝ := Real.sqrt (momSq k)

theorem mAbs_nonneg (k : Mom) : 0 ≤ mAbs k := Real.sqrt_nonneg _

theorem mAbs_sq (k : Mom) : mAbs k ^ 2 = momSq k := Real.sq_sqrt (momSq_nonneg k)

theorem abs_k_le_mAbs (k : Mom) (mu : Fin 3) : |((k mu : ℤ) : ℝ)| ≤ mAbs k := by
  have h : |((k mu : ℤ) : ℝ)| = Real.sqrt (((k mu : ℤ) : ℝ) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [h, mAbs]
  exact Real.sqrt_le_sqrt (sq_le_momSq k mu)

/-! ### The forms evaluated on a field configuration -/

/-- The value of the linear form `F` at momentum `k` on a field configuration `z`. -/
def formValue (k : Mom) (F : FormIdx) (z : Comp → ℂ) : ℂ := ∑ c : Comp, gCoef k F c * z c

theorem formValue_torsion (k : Mom) (mu nu i : Fin 3) (z : Comp → ℂ) :
    formValue k (torsionF mu nu i) z = z (dIdx mu nu i) - z (dIdx nu mu i) := by
  simp only [formValue, gCoef_torsion, sub_mul, Finset.sum_sub_distrib, sum_ind_mul]

/-- **The gauge fixing of the derivative variables**: the form is `D_{μν}^i − i k_μ e_ν^i`,
so its vanishing says exactly that the independent coordinate `D_{μν}^i` is the spatial
derivative `∂_μ e_ν^i` of the field. -/
theorem formValue_dGauge (k : Mom) (mu nu i : Fin 3) (z : Comp → ℂ) :
    formValue k (dGaugeF mu nu i) z
      = z (dIdx mu nu i) - Complex.I * ((k mu : ℤ) : ℂ) * z (eIdx nu i) := by
  have h : ∀ c : Comp, gCoef k (dGaugeF mu nu i) c * z c
      = ind c (dIdx mu nu i) * z c
        - (Complex.I * ((k mu : ℤ) : ℂ)) * (ind c (eIdx nu i) * z c) := by
    intro c
    rw [gCoef_dGauge]
    ring
  rw [formValue, Finset.sum_congr rfl fun c _ => h c, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_ind_mul, sum_ind_mul, mul_assoc]

/-- **The 3D gauge fixing**: the transverse condition `Σ_μ i k_μ e_μ^i = 0`. -/
theorem formValue_gauge3d (k : Mom) (i : Fin 3) (z : Comp → ℂ) :
    formValue k (gauge3dF i) z
      = ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * z (eIdx mu i) := by
  have h : ∀ c : Comp, gCoef k (gauge3dF i) c * z c
      = ∑ mu : Fin 3, (Complex.I * ((k mu : ℤ) : ℂ)) * (ind c (eIdx mu i) * z c) := by
    intro c
    rw [gCoef_gauge3d, Finset.sum_mul]
    exact Finset.sum_congr rfl fun mu _ => by ring
  rw [formValue, Finset.sum_congr rfl fun c _ => h c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun mu _ => ?_
  rw [← Finset.mul_sum, sum_ind_mul, mul_assoc]

/-- **The complete quadratic form of the gauge-fixed gravity Hamiltonian in the extended
variables**: the Gram matrix of the torsion forms, the derivative-gauge forms and the 3D
gauge-fixing forms.  It is diagonal in the momentum and a full `36 × 36` matrix in the
components at each momentum. -/
def gGram (x y : GMode) : ℂ :=
  if x.1 = y.1 then
    ∑ F : FormIdx, (starRingEnd ℂ) (gCoef x.1 F x.2) * gCoef x.1 F y.2
  else 0

end BookProof.QgFourierElim


