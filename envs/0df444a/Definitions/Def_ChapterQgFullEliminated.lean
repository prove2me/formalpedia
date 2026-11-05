-- Prove2me | Definitions.Def_ChapterQgFullEliminated
-- name    : ChapterQgFullEliminated
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T13:39:44.974858+00:00
-- url     : https://prove2.me/theorems/d6cc4795-6fe5-4cfa-a676-25cac4ae740b
-- title:
--   Chapter QgFullEliminated
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgFullEliminated.lean`): generated def bundle for ChapterQgFullEliminated. See BookProof/ChapterQgFullEliminated.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgFullEliminated.lean

import Definitions.Def_ChapterQgFourierElimination
import Theorems.Thm_BookProof_QgFourierElim_formValue_torsion_elimConfig
import Theorems.Thm_BookProof_QgFourierElim_formValue_dGauge_elimConfig
import Theorems.Thm_BookProof_QgFourierElim_formValue_gauge3d_elimConfig
import Theorems.Thm_BookProof_QgFourierElim_eq_elimConfig_of_gauge_fixed
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_esa_on_core
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterStoneBridge
import Mathlib
import Definitions.Def_ChapterQgFourierElimForms
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Theorems.Thm_BookProof_QgOuterFockCoreFL_commForm_congr
import Theorems.Thm_BookProof_QgOuterFockCoreFL_quadForm_congr
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa


/-!
# The full quantum-gravity Hamiltonian rebuilt on the eliminated components alone

Second half of item 8 of the quantum-gravity plan items of `CONSOLIDATED_PLAN.md`.  The model of
`BookProof/ChapterQgVielbeinScalaronGaugeFL.lean` carries `36` components per momentum — the nine
vielbein components `e_ν^i(k)` *and* the twenty-seven independent derivative variables
`D_{μν}^i(k)` — and imposes the derivative-gauge forms `G_{μν}^i = D_{μν}^i − i k_μ e_ν^i` as part
of the quadratic form.  `BookProof/ChapterQgFourierElimination.lean` §4 shows that the derivative
components carry no independent content: the constraint surface is exactly the image of the
elimination `elimConfig`.

Here the whole Hamiltonian — vielbein self-interaction (torsion), derivative gauge fixing, 3D
transverse gauge fixing, the scalaron in position representation with the full exponential
Einstein-frame wall, and the coupling to the trace of the vielbein — is **rebuilt on the nine
eliminated components alone**, and its essential self-adjointness is proved again, by the same
Faris–Lavine route, on the smaller outer Fock space `Sec EGMode`.

What is proved, in order:

* `elimCoef` — the coefficient vector, *in the nine vielbein components only*, of each of the `57`
  linear forms of the full model after the elimination `D_{μν}^i ↦ i k_μ e_ν^i`;
  `eFormValue_eq_formValue_elimConfig` is the defining property (the eliminated form is the full
  form evaluated on the eliminated configuration), `elimCoef_dGauge` records that the twenty-seven
  derivative-gauge forms become identically zero, and `eFormValue_torsion` that the torsion form
  becomes the exact Fourier torsion `i(k_μ e_ν^i − k_ν e_μ^i)`.
* `eGram` — the vielbein self-interaction of the rebuilt model, the Gram matrix of the eliminated
  family; `eGram_eq_torsion_add_gauge3d` exhibits it as torsion plus transverse gauge fixing (the
  derivative-gauge forms contributing nothing), and `eGram_quadForm` /
  `quadForm_eq_of_gauge_fixed` prove that **the rebuilt quadratic form is the full one restricted
  to the gauge surface**, in the nine surviving coordinates.
* `eCoupling` — the scalaron–vielbein coupling, unchanged (`eTrace_eq_gTrace`: the trace the
  scalaron couples to never involved the derivative components).
* `qgElimFullModes` — the mode data of the rebuilt model: all five Faris–Lavine bounds with
  `κ = 513 + |g|` and band size `9` (instead of `36`).
* `qgElimFull_esa_farisLavine`, `qgElimFull_esa_core_fl`, `starobinsky_qgElimFull_esa`,
  `starobinsky_qgElimFull_esa_core` — essential self-adjointness of the rebuilt Hamiltonian, and
  `qgElimFull_stone_flow` / `starobinsky_qgElimFull_stone_flow` the unitary time evolution it
  generates.  The extended derivative components never enter the operator or its domain, and no
  restriction-to-a-subset argument is used.
* `qgElimFull_momentum_conserving`, `qgElimFull_number_conserving` — the rebuilt Hamiltonian is
  still block diagonal in the momentum and conserves the particle number.
* Non-vacuity: `elimCoef_torsion_ne_zero`, `elimCoef_gauge3d_ne_zero`, `eGram_diag_ne_zero`,
  `eCoupling_ne_zero`, `infinite_egmode`.

No spectral information, no mass gap and no continuum limit is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgFullEliminated

open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.DirectSumEsa BookProof.ScalaronEsa
open BookProof.QgFourierElim

noncomputable section

/-! ## 1. The eliminated components and their modes -/

/-- The surviving field-space components at one momentum: the nine vielbein components `e_ν^i`.
The twenty-seven derivative components of the full model are gone — not gauge fixed, *absent*. -/
abbrev EComp := Fin 3 × Fin 3

/-- A mode of the rebuilt model: a momentum in `ℤ³` together with one of the nine vielbein
components.  There are still infinitely many momenta — no lattice, no truncation. -/
abbrev EGMode := Mom × EComp

/-- The energy of a mode: the same exact free symbol `σ_k = 1 + |k|²` as in the full model. -/
def eSig (x : EGMode) : ℝ := 1 + momSq x.1

theorem one_le_eSig (x : EGMode) : 1 ≤ eSig x := by
  have := momSq_nonneg x.1
  simp only [eSig]
  linarith

theorem eSig_nonneg (x : EGMode) : 0 ≤ eSig x := le_trans zero_le_one (one_le_eSig x)

/-- The band of a mode: the nine components at the same momentum. -/
def eNbr (x : EGMode) : Finset EGMode :=
  ({x.1} : Finset Mom) ×ˢ (Finset.univ : Finset EComp)

theorem mem_eNbr {x y : EGMode} : y ∈ eNbr x ↔ y.1 = x.1 := by
  constructor
  · intro h
    simp only [eNbr, Finset.mem_product, Finset.mem_singleton] at h
    exact h.1
  · intro h
    simp only [eNbr, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
    exact h

theorem card_eNbr (x : EGMode) : ((eNbr x).card : ℝ) = 9 := by
  simp [eNbr]

/-! ## 2. The linear forms of the full model, after the elimination -/

/-- The indicator of an eliminated component. -/
def eind (c d : EComp) : ℂ := if c = d then 1 else 0

theorem norm_eind_le (c d : EComp) : ‖eind c d‖ ≤ 1 := by
  simp only [eind]; split <;> simp

theorem sum_eind_mul (d : EComp) (z : EComp → ℂ) : ∑ c : EComp, eind c d * z c = z d := by
  classical
  rw [Finset.sum_eq_single d]
  · simp [eind]
  · intro c _ hc
    simp [eind, hc]
  · intro h
    exact absurd (Finset.mem_univ d) h

/-- **The coefficient vectors of the three families of linear forms after the elimination.**  Each
form of the full model is rewritten, by `D_{μν}^i ↦ i k_μ e_ν^i`, as a linear form in the nine
vielbein components alone:

* the torsion form becomes the exact Fourier torsion `i(k_μ e_ν^i − k_ν e_μ^i)`;
* the derivative-gauge form becomes identically zero — the constraint is solved, not imposed;
* the 3D transverse form is untouched. -/
def elimCoef (k : Mom) : FormIdx → EComp → ℂ
  | Sum.inl (mu, nu, i), c =>
      Complex.I * ((k mu : ℤ) : ℂ) * eind c (nu, i)
        - Complex.I * ((k nu : ℤ) : ℂ) * eind c (mu, i)
  | Sum.inr (Sum.inl _), _ => 0
  | Sum.inr (Sum.inr i), c => ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * eind c (mu, i)

@[simp] theorem elimCoef_torsion (k : Mom) (mu nu i : Fin 3) (c : EComp) :
    elimCoef k (torsionF mu nu i) c
      = Complex.I * ((k mu : ℤ) : ℂ) * eind c (nu, i)
          - Complex.I * ((k nu : ℤ) : ℂ) * eind c (mu, i) := rfl

/-- **The derivative-gauge forms disappear**: after the elimination they are the zero form, which
is the formal statement that the twenty-seven constraints are solved by construction. -/
@[simp] theorem elimCoef_dGauge (k : Mom) (mu nu i : Fin 3) (c : EComp) :
    elimCoef k (dGaugeF mu nu i) c = 0 := rfl

@[simp] theorem elimCoef_gauge3d (k : Mom) (i : Fin 3) (c : EComp) :
    elimCoef k (gauge3dF i) c = ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * eind c (mu, i) :=
  rfl

/-- The value of the eliminated form `F` at momentum `k` on a configuration of the nine vielbein
components. -/
def eFormValue (k : Mom) (F : FormIdx) (z : EComp → ℂ) : ℂ := ∑ c : EComp, elimCoef k F c * z c

/-- **The eliminated torsion form is the exact Fourier torsion.** -/
theorem eFormValue_torsion (k : Mom) (mu nu i : Fin 3) (z : EComp → ℂ) :
    eFormValue k (torsionF mu nu i) z
      = Complex.I * ((k mu : ℤ) : ℂ) * z (nu, i) - Complex.I * ((k nu : ℤ) : ℂ) * z (mu, i) := by
  have h : ∀ c : EComp, elimCoef k (torsionF mu nu i) c * z c
      = (Complex.I * ((k mu : ℤ) : ℂ)) * (eind c (nu, i) * z c)
        - (Complex.I * ((k nu : ℤ) : ℂ)) * (eind c (mu, i) * z c) := by
    intro c
    rw [elimCoef_torsion]
    ring
  rw [eFormValue, Finset.sum_congr rfl fun c _ => h c, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_eind_mul, sum_eind_mul]

/-- **The eliminated derivative-gauge form vanishes identically.** -/
theorem eFormValue_dGauge (k : Mom) (mu nu i : Fin 3) (z : EComp → ℂ) :
    eFormValue k (dGaugeF mu nu i) z = 0 := by
  simp [eFormValue]

/-- The 3D transverse form is unchanged by the elimination. -/
theorem eFormValue_gauge3d (k : Mom) (i : Fin 3) (z : EComp → ℂ) :
    eFormValue k (gauge3dF i) z = ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * z (mu, i) := by
  have h : ∀ c : EComp, elimCoef k (gauge3dF i) c * z c
      = ∑ mu : Fin 3, (Complex.I * ((k mu : ℤ) : ℂ)) * (eind c (mu, i) * z c) := by
    intro c
    rw [elimCoef_gauge3d, Finset.sum_mul]
    exact Finset.sum_congr rfl fun mu _ => by ring
  rw [eFormValue, Finset.sum_congr rfl fun c _ => h c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun mu _ => ?_
  rw [← Finset.mul_sum, sum_eind_mul]

/-- **The defining property of the elimination**: the eliminated form is the full form of
`ChapterQgVielbeinScalaronGaugeFL` evaluated on the eliminated configuration.  Nothing is added
and nothing is dropped; the rebuilt model is the full model written in the nine surviving
coordinates. -/
theorem eFormValue_eq_formValue_elimConfig (k : Mom) (F : FormIdx) (z : EComp → ℂ) :
    formValue k F (elimConfig k z) = eFormValue k F z := by
  rcases F with ⟨mu, nu, i⟩ | (⟨mu, nu, i⟩ | i)
  · have hF : (Sum.inl (mu, nu, i) : FormIdx) = torsionF mu nu i := rfl
    rw [hF, formValue_torsion_elimConfig, eFormValue_torsion]
    ring
  · have hF : (Sum.inr (Sum.inl (mu, nu, i)) : FormIdx) = dGaugeF mu nu i := rfl
    rw [hF, formValue_dGauge_elimConfig, eFormValue_dGauge]
  · have hF : (Sum.inr (Sum.inr i) : FormIdx) = gauge3dF i := rfl
    rw [hF, formValue_gauge3d_elimConfig, eFormValue_gauge3d]

/-! ### The uniform bounds on the eliminated coefficients -/

theorem norm_I_mul_k_mul_eind (k : Mom) (mu : Fin 3) (c d : EComp) :
    ‖Complex.I * ((k mu : ℤ) : ℂ) * eind c d‖ ≤ mAbs k := by
  have h1 : ‖Complex.I * ((k mu : ℤ) : ℂ) * eind c d‖
      = |((k mu : ℤ) : ℝ)| * ‖eind c d‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    congr 1
    simp
  rw [h1]
  have h2 := norm_eind_le c d
  have h3 := abs_k_le_mAbs k mu
  have h4 : (0 : ℝ) ≤ |((k mu : ℤ) : ℝ)| := abs_nonneg _
  nlinarith [norm_nonneg (eind c d)]

/-- Every eliminated coefficient is bounded by `3|k|`: the elimination replaces the bounded
derivative coordinates by momentum weights, so all three families are now `O(|k|)`. -/
theorem norm_elimCoef_le (k : Mom) (F : FormIdx) (c : EComp) : ‖elimCoef k F c‖ ≤ 3 * mAbs k := by
  have hM := mAbs_nonneg k
  rcases F with ⟨mu, nu, i⟩ | (⟨mu, nu, i⟩ | i)
  · have hF : elimCoef k (Sum.inl (mu, nu, i)) c = elimCoef k (torsionF mu nu i) c := rfl
    have h : ‖elimCoef k (torsionF mu nu i) c‖ ≤ mAbs k + mAbs k :=
      le_trans (norm_sub_le _ _)
        (add_le_add (norm_I_mul_k_mul_eind k mu c (nu, i))
          (norm_I_mul_k_mul_eind k nu c (mu, i)))
    rw [hF]
    linarith
  · have hF : elimCoef k (Sum.inr (Sum.inl (mu, nu, i))) c = elimCoef k (dGaugeF mu nu i) c := rfl
    rw [hF, elimCoef_dGauge, norm_zero]
    linarith
  · have hF : elimCoef k (Sum.inr (Sum.inr i)) c = elimCoef k (gauge3dF i) c := rfl
    have h : ‖elimCoef k (gauge3dF i) c‖ ≤ 3 * mAbs k := by
      rw [elimCoef_gauge3d]
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ mu : Fin 3, ‖Complex.I * ((k mu : ℤ) : ℂ) * eind c (mu, i)‖
          ≤ ∑ _mu : Fin 3, mAbs k :=
            Finset.sum_le_sum fun mu _ => norm_I_mul_k_mul_eind k mu c (mu, i)
        _ = 3 * mAbs k := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
    rw [hF]
    linarith

theorem norm_elimCoef_mul_le (k : Mom) (F : FormIdx) (c d : EComp) :
    ‖(starRingEnd ℂ) (elimCoef k F c) * elimCoef k F d‖ ≤ 9 * (1 + momSq k) := by
  rw [norm_mul, RCLike.norm_conj]
  have h1 := norm_elimCoef_le k F c
  have h2 := norm_elimCoef_le k F d
  have hM := mAbs_nonneg k
  have hsq := mAbs_sq k
  nlinarith [norm_nonneg (elimCoef k F c), norm_nonneg (elimCoef k F d), sq_nonneg (mAbs k)]

/-! ## 3. The vielbein self-interaction of the rebuilt model -/

/-- **The complete quadratic form of the full model, rebuilt on the nine eliminated components**:
the Gram matrix of the eliminated torsion forms, the (vanishing) eliminated derivative-gauge forms
and the 3D transverse forms.  It is diagonal in the momentum and a `9 × 9` matrix in the
components at each momentum. -/
def eGram (x y : EGMode) : ℂ :=
  if x.1 = y.1 then
    ∑ F : FormIdx, (starRingEnd ℂ) (elimCoef x.1 F x.2) * elimCoef x.1 F y.2
  else 0

theorem eGram_herm (x y : EGMode) : eGram y x = (starRingEnd ℂ) (eGram x y) := by
  by_cases h : x.1 = y.1
  · have hy : y.1 = x.1 := h.symm
    simp only [eGram]
    rw [if_pos hy, if_pos h, hy, map_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring
  · simp only [eGram, if_neg h, if_neg (Ne.symm h), map_zero]

theorem eGram_off {x y : EGMode} (h : y ∉ eNbr x) : eGram x y = 0 := by
  have hne : ¬ x.1 = y.1 := fun hh => h (mem_eNbr.mpr hh.symm)
  simp only [eGram, if_neg hne]

theorem norm_eGram_le (x y : EGMode) : ‖eGram x y‖ ≤ 513 * eSig x := by
  by_cases h : x.1 = y.1
  · simp only [eGram, if_pos h]
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ F : FormIdx, ‖(starRingEnd ℂ) (elimCoef x.1 F x.2) * elimCoef x.1 F y.2‖
        ≤ ∑ _F : FormIdx, 9 * (1 + momSq x.1) :=
          Finset.sum_le_sum fun F _ => norm_elimCoef_mul_le x.1 F x.2 y.2
      _ = 57 * (9 * (1 + momSq x.1)) := by
          rw [Finset.sum_const, Finset.card_univ, card_formIdx, nsmul_eq_mul]
          norm_num
      _ = 513 * eSig x := by simp only [eSig]; ring
  · have hnn := eSig_nonneg x
    simp only [eGram, if_neg h, norm_zero]
    linarith

/-- **The rebuilt self-interaction is torsion plus transverse gauge fixing**: the twenty-seven
derivative-gauge forms contribute nothing, because the elimination solves them identically. -/
theorem eGram_eq_torsion_add_gauge3d (k : Mom) (c d : EComp) :
    eGram (k, c) (k, d)
      = (∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3,
            (starRingEnd ℂ) (elimCoef k (torsionF mu nu i) c) * elimCoef k (torsionF mu nu i) d)
        + ∑ i : Fin 3,
            (starRingEnd ℂ) (elimCoef k (gauge3dF i) c) * elimCoef k (gauge3dF i) d := by
  have hd : ∀ p : Fin 3 × Fin 3 × Fin 3,
      (starRingEnd ℂ) (elimCoef k (Sum.inr (Sum.inl p)) c) * elimCoef k (Sum.inr (Sum.inl p)) d
        = 0 := by
    intro p
    obtain ⟨mu, nu, i⟩ := p
    have hF : (Sum.inr (Sum.inl (mu, nu, i)) : FormIdx) = dGaugeF mu nu i := rfl
    simp only [hF, elimCoef_dGauge, map_zero, zero_mul]
  have htor : (∑ p : Fin 3 × Fin 3 × Fin 3,
        (starRingEnd ℂ) (elimCoef k (Sum.inl p) c) * elimCoef k (Sum.inl p) d)
      = ∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3,
          (starRingEnd ℂ) (elimCoef k (torsionF mu nu i) c)
            * elimCoef k (torsionF mu nu i) d := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun mu _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  have hgauge : (∑ p : (Fin 3 × Fin 3 × Fin 3) ⊕ Fin 3,
        (starRingEnd ℂ) (elimCoef k (Sum.inr p) c) * elimCoef k (Sum.inr p) d)
      = ∑ i : Fin 3, (starRingEnd ℂ) (elimCoef k (gauge3dF i) c) * elimCoef k (gauge3dF i) d := by
    rw [Fintype.sum_sum_type, Finset.sum_congr rfl fun p _ => hd p, Finset.sum_const_zero,
      zero_add]
    rfl
  have hsplit : eGram (k, c) (k, d)
      = (∑ p : Fin 3 × Fin 3 × Fin 3,
            (starRingEnd ℂ) (elimCoef k (Sum.inl p) c) * elimCoef k (Sum.inl p) d)
        + ∑ p : (Fin 3 × Fin 3 × Fin 3) ⊕ Fin 3,
            (starRingEnd ℂ) (elimCoef k (Sum.inr p) c) * elimCoef k (Sum.inr p) d := by
    have hval : eGram ((k, c) : EGMode) (k, d)
        = ∑ F : FormIdx, (starRingEnd ℂ) (elimCoef k F c) * elimCoef k F d := by
      simp [eGram]
    rw [hval, Fintype.sum_sum_type]
  rw [hsplit, htor, hgauge]

/-! ### The rebuilt quadratic form is the full one on the gauge surface -/

/-- A Gram matrix built from a family of linear forms evaluates, as a quadratic form, to the sum
of the squared moduli of the values of the forms. -/
theorem gram_quadForm {X : Type*} [Fintype X] (C : FormIdx → X → ℂ) (z : X → ℂ) :
    ∑ c : X, ∑ d : X,
        (starRingEnd ℂ) (z c) * ((∑ F : FormIdx, (starRingEnd ℂ) (C F c) * C F d) * z d)
      = ∑ F : FormIdx, (starRingEnd ℂ) (∑ c : X, C F c * z c) * (∑ d : X, C F d * z d) := by
  have hL : ∀ c : X, ∀ d : X,
      (starRingEnd ℂ) (z c) * ((∑ F : FormIdx, (starRingEnd ℂ) (C F c) * C F d) * z d)
        = ∑ F : FormIdx,
            (starRingEnd ℂ) (z c) * ((starRingEnd ℂ) (C F c) * C F d) * z d := by
    intro c d
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun F _ => by ring
  have hR : ∀ F : FormIdx,
      (starRingEnd ℂ) (∑ c : X, C F c * z c) * (∑ d : X, C F d * z d)
        = ∑ c : X, ∑ d : X, (starRingEnd ℂ) (z c) * ((starRingEnd ℂ) (C F c) * C F d) * z d := by
    intro F
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul]
    ring
  calc ∑ c : X, ∑ d : X,
        (starRingEnd ℂ) (z c) * ((∑ F : FormIdx, (starRingEnd ℂ) (C F c) * C F d) * z d)
      = ∑ c : X, ∑ d : X, ∑ F : FormIdx,
          (starRingEnd ℂ) (z c) * ((starRingEnd ℂ) (C F c) * C F d) * z d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => hL c d
    _ = ∑ c : X, ∑ F : FormIdx, ∑ d : X,
          (starRingEnd ℂ) (z c) * ((starRingEnd ℂ) (C F c) * C F d) * z d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ F : FormIdx, ∑ c : X, ∑ d : X,
          (starRingEnd ℂ) (z c) * ((starRingEnd ℂ) (C F c) * C F d) * z d :=
        Finset.sum_comm
    _ = ∑ F : FormIdx, (starRingEnd ℂ) (∑ c : X, C F c * z c) * (∑ d : X, C F d * z d) :=
        Finset.sum_congr rfl fun F _ => (hR F).symm

/-- The rebuilt quadratic form at one momentum is the sum of the squared moduli of the eliminated
forms. -/
theorem eGram_quadForm (k : Mom) (z : EComp → ℂ) :
    ∑ c : EComp, ∑ d : EComp, (starRingEnd ℂ) (z c) * (eGram (k, c) (k, d) * z d)
      = ∑ F : FormIdx, (starRingEnd ℂ) (eFormValue k F z) * eFormValue k F z := by
  have h : ∀ c d : EComp, eGram (k, c) (k, d)
      = ∑ F : FormIdx, (starRingEnd ℂ) (elimCoef k F c) * elimCoef k F d := by
    intro c d
    simp [eGram]
  simp only [h, eFormValue]
  exact gram_quadForm (X := EComp) (elimCoef k) z

/-- The full quadratic form at one momentum is the sum of the squared moduli of the full forms. -/
theorem gGram_quadForm (k : Mom) (w : Comp → ℂ) :
    ∑ c : Comp, ∑ d : Comp, (starRingEnd ℂ) (w c) * (gGram (k, c) (k, d) * w d)
      = ∑ F : FormIdx, (starRingEnd ℂ) (formValue k F w) * formValue k F w := by
  have h : ∀ c d : Comp, gGram ((k, c) : GMode) (k, d)
      = ∑ F : FormIdx, (starRingEnd ℂ) (gCoef k F c) * gCoef k F d := by
    intro c d
    simp [gGram]
  simp only [h, formValue]
  exact gram_quadForm (X := Comp) (gCoef k) w

/-- **The rebuilt Hamiltonian carries the full quadratic form.**  On the gauge surface — where the
twenty-seven derivative-gauge constraints of the full model hold — the `36`-component quadratic
form of `ChapterQgVielbeinScalaronGaugeFL` and the `9`-component quadratic form rebuilt here take
the same value, the latter evaluated on the vielbein part of the configuration.  Together with
`eq_elimConfig_of_gauge_fixed` (every gauge-fixed configuration is an eliminated one) this is the
sense in which nothing is lost by discarding the derivative components. -/
theorem quadForm_eq_of_gauge_fixed (k : Mom) (w : Comp → ℂ)
    (hgauge : ∀ mu nu i, formValue k (dGaugeF mu nu i) w = 0) :
    ∑ c : Comp, ∑ d : Comp, (starRingEnd ℂ) (w c) * (gGram (k, c) (k, d) * w d)
      = ∑ c : EComp, ∑ d : EComp,
          (starRingEnd ℂ) (w (eIdx c.1 c.2)) *
            (eGram (k, c) (k, d) * w (eIdx d.1 d.2)) := by
  set z : EComp → ℂ := fun p => w (eIdx p.1 p.2) with hz
  have hw : w = elimConfig k z := eq_elimConfig_of_gauge_fixed k w hgauge
  rw [gGram_quadForm k w, eGram_quadForm k z]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [hw, eFormValue_eq_formValue_elimConfig]

/-! ## 4. The scalaron–vielbein coupling on the eliminated components -/

/-- The trace part of the vielbein: the combination the scalaron couples to.  It only ever
involved the nine vielbein components, so the elimination leaves it unchanged. -/
def eTrace (x : EGMode) : ℝ := if x.2.1 = x.2.2 then 1 else 0

/-- The trace part of the vielbein: the combination the scalaron couples to.  The derivative
variables do not carry it. -/
def gTrace (x : GMode) : ℝ :=
  match x.2 with
  | Sum.inl (nu, i) => if nu = i then 1 else 0
  | Sum.inr _ => 0

/-- The trace of the rebuilt model is the trace of the full model, read on the vielbein
components. -/
theorem eTrace_eq_gTrace (x : EGMode) : eTrace x = gTrace (x.1, eIdx x.2.1 x.2.2) := rfl

theorem abs_eTrace_le (x : EGMode) : |eTrace x| ≤ 1 := by
  simp only [eTrace]
  split <;> simp

/-- **The scalaron–vielbein coupling** at coupling constant `g`, on the eliminated components. -/
def eCoupling (g : ℝ) (x y : EGMode) : ℂ :=
  if x.1 = y.1 then ((g * eTrace x * eTrace y : ℝ) : ℂ) else 0

theorem eCoupling_herm (g : ℝ) (x y : EGMode) :
    eCoupling g y x = (starRingEnd ℂ) (eCoupling g x y) := by
  by_cases h : x.1 = y.1
  · have hy : y.1 = x.1 := h.symm
    simp only [eCoupling]
    rw [if_pos hy, if_pos h, Complex.conj_ofReal]
    norm_cast
    ring
  · simp only [eCoupling, if_neg h, if_neg (Ne.symm h), map_zero]

theorem eCoupling_off (g : ℝ) {x y : EGMode} (h : y ∉ eNbr x) : eCoupling g x y = 0 := by
  have hne : ¬ x.1 = y.1 := fun hh => h (mem_eNbr.mpr hh.symm)
  simp only [eCoupling, if_neg hne]

theorem norm_eCoupling_le (g : ℝ) (x y : EGMode) : ‖eCoupling g x y‖ ≤ |g| := by
  by_cases h : x.1 = y.1
  · simp only [eCoupling, if_pos h, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 := abs_eTrace_le x
    have h2 := abs_eTrace_le y
    have hg := abs_nonneg g
    calc |g| * |eTrace x| * |eTrace y| ≤ |g| * 1 * 1 := by gcongr
      _ = |g| := by ring
  · simp only [eCoupling, if_neg h, norm_zero]
    exact abs_nonneg g

/-! ## 5. The mode data of the rebuilt model -/

/-- **The mode data of the full quantum-gravity model rebuilt on the eliminated components**:
exact Fourier modes of the vielbein, the torsion self-interaction in its eliminated (exact
Fourier) form, the — now identically satisfied — gauge fixing of the derivative variables, the 3D
transverse gauge fixing and the scalaron coupling.  All five Faris–Lavine bounds hold with the
single constant `κ = 513 + |g|` and band size `9`, uniformly in the momentum. -/
def qgElimFullModes (g : ℝ) : QgModeData EGMode :=
  ofBounds eSig one_le_eSig eGram (eCoupling g) eNbr
    (fun a b => by rw [mem_eNbr, mem_eNbr, eq_comm])
    (fun _ _ hb => eGram_off hb) (fun _ _ hb => eCoupling_off g hb)
    eGram_herm (eCoupling_herm g)
    (513 + |g|) 9 (by positivity) (by norm_num)
    (fun a => le_of_eq (card_eNbr a))
    (fun a b => by
      by_cases h : a.1 = b.1
      · have hmin : min (eSig a) (eSig b) = eSig a := by
          simp only [eSig]
          rw [h]
          exact min_self _
        have hb := norm_eGram_le a b
        have hnn := eSig_nonneg a
        have hg := abs_nonneg g
        rw [hmin]
        nlinarith
      · have hz : eGram a b = 0 := by simp only [eGram, if_neg h]
        have h1 : (1 : ℝ) ≤ min (eSig a) (eSig b) := le_min (one_le_eSig a) (one_le_eSig b)
        have hg := abs_nonneg g
        rw [hz, norm_zero]
        nlinarith)
    (fun a b => le_trans (norm_eCoupling_le g a b) (by norm_num))
    (fun a b hb => by
      have h : b.1 = a.1 := mem_eNbr.mp hb
      have hcs : eSig a = eSig b := by simp only [eSig, h]
      have hg := abs_nonneg g
      rw [hcs, sub_self, abs_zero]
      linarith)

@[simp] theorem qgElimFullModes_sig (g : ℝ) : (qgElimFullModes g).sig = eSig := rfl

@[simp] theorem qgElimFullModes_A (g : ℝ) : (qgElimFullModes g).A = eGram := rfl

@[simp] theorem qgElimFullModes_B (g : ℝ) : (qgElimFullModes g).B = eCoupling g := rfl

@[simp] theorem qgElimFullModes_nbr (g : ℝ) : (qgElimFullModes g).nbr = eNbr := rfl

/-! ## 6. Essential self-adjointness of the rebuilt Hamiltonian, by Faris–Lavine -/

/-- **Essential self-adjointness of the full gauge-fixed quantum-gravity Hamiltonian, rebuilt on
the eliminated components alone.**

The Hamiltonian carries, at once: the vielbein in its exact Fourier modes (no lattice, no
truncation), the torsion self-interaction in the exact Fourier form the elimination produces, the
derivative-gauge condition — now solved by construction rather than imposed — the 3D transverse
gauge fixing, and the scalaron in position representation with an arbitrary smooth non-negative
wall coupled to the trace of the vielbein at arbitrary coupling constant `g`.  The twenty-seven
derivative components of `ChapterQgVielbeinScalaronGaugeFL` occur neither in the operator nor in
its domain, and no restriction-to-a-subset argument is used.

The proof is Theorem 1 of Faris–Lavine against the `ℓ²`-lift of the Friedrichs extension of the
positive fibre operator `−∂²_φ + φ²/4 + V(φ) + σ_a`. -/
theorem qgElimFull_esa_farisLavine (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (secN W (qgElimFullModes g)).dom
      (secData W (qgElimFullModes g)).ext :=
  secHam_essentiallySelfAdjointOn W _

/-- The self-adjoint realization restricts to the rebuilt Hamiltonian on the finite-particle
core. -/
theorem qgElimFull_ext_core (W : WallPot) (g : ℝ) (p : secCore (ι := EGMode)) :
    (secData W (qgElimFullModes g)).ext
        ⟨(p : Sec EGMode), (secData W (qgElimFullModes g)).gc.le p.2⟩
      = secHam W (qgElimFullModes g) p :=
  secData_ext_core W _ p

/-- **The same on the finite-particle core**, where the rebuilt Hamiltonian is originally
defined. -/
theorem qgElimFull_esa_core_fl (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (secCore (ι := EGMode)) (secHam W (qgElimFullModes g)) := by
  refine (secData W (qgElimFullModes g)).esa_on_core (secHam_symmetricOn W _)
    (c := 6 * (qgElimFullModes g).K) (by have := (qgElimFullModes g).K_nonneg; linarith) ?_
  intro p
  have hc : commForm (secData W (qgElimFullModes g)).H₀ (secData W (qgElimFullModes g)).coreN p
      = commForm (secHam W (qgElimFullModes g)) (secDiag W (qgElimFullModes g)) p :=
    commForm_congr _ _ _ _ _ _ rfl (secData_coreN W (qgElimFullModes g) p)
  have hq : quadForm (secData W (qgElimFullModes g)).coreN p
      = quadForm (secDiag W (qgElimFullModes g)) p :=
    quadForm_congr _ _ _ _ rfl (secData_coreN W (qgElimFullModes g) p)
  rw [hc, hq]
  exact secHam_commForm_le W (qgElimFullModes g) p

/-- **The physical instance**: the full exponential Einstein-frame Starobinsky potential. -/
theorem starobinsky_qgElimFull_esa (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) :
    EssentiallySelfAdjointOn (secN (starobinskyWall M alpha halpha) (qgElimFullModes g)).dom
      (secData (starobinskyWall M alpha halpha) (qgElimFullModes g)).ext :=
  qgElimFull_esa_farisLavine (starobinskyWall M alpha halpha) g

/-- The physical instance on the finite-particle core. -/
theorem starobinsky_qgElimFull_esa_core (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) :
    EssentiallySelfAdjointOn (secCore (ι := EGMode))
      (secHam (starobinskyWall M alpha halpha) (qgElimFullModes g)) :=
  qgElimFull_esa_core_fl (starobinskyWall M alpha halpha) g

/-! ## 6b. The unitary time evolution -/

/-- The finite-particle core is dense in the outer Fock space of the rebuilt model. -/
theorem eSecCore_dense :
    Dense ((secCore (ι := EGMode) : Submodule ℂ (Sec EGMode)) : Set (Sec EGMode)) :=
  dsCore_dense fun _ => ccDomain_dense

/-- **The unitary flow of the rebuilt Hamiltonian**, by Stone's theorem. -/
theorem qgElimFull_stone_flow (W : WallPot) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec EGMode))
      (U : ℝ → (Sec EGMode →L[ℂ] Sec EGMode)),
      IsSelfAdjointExtension (secHam W (qgElimFullModes g)) T.op ∧
        IsStoneFlow T U :=
  exists_stone_flow_of_esa _ eSecCore_dense (secHam_symmetricOn W _)
    (qgElimFull_esa_core_fl W g)

/-- The physical instance of the flow, with the full exponential Einstein-frame Starobinsky
potential. -/
theorem starobinsky_qgElimFull_stone_flow (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec EGMode))
      (U : ℝ → (Sec EGMode →L[ℂ] Sec EGMode)),
      IsSelfAdjointExtension
          (secHam (starobinskyWall M alpha halpha) (qgElimFullModes g)) T.op ∧
        IsStoneFlow T U :=
  qgElimFull_stone_flow (starobinskyWall M alpha halpha) g

/-! ## 7. Momentum and particle-number conservation -/

section QgFullNumber
variable {ι : Type*}

/-- **The outer Hamiltonian conserves the particle number.**  For any assignment of a
particle number to the modes that is constant on the bands, the sector of a fixed particle
number is invariant: a core vector supported in the sector `num = n` is mapped by the
Hamiltonian to a vector supported in the same sector.  No lattice regularization is
involved: the number sectors, not a spatial cutoff, are what makes the outer Hamiltonian
block diagonal. -/
theorem secHam_number_conserving (W : WallPot) (Q : QgModeData ι) {num : ι → ℕ}
    (hnum : ∀ a b, b ∈ Q.nbr a → num b = num a) (x : secCore (ι := ι)) {n : ℕ}
    (hx : ∀ a, num a ≠ n → (x : Sec ι) a = 0) (a : ι) (ha : num a ≠ n) :
    (secHam W Q x : Sec ι) a = 0 := by
  have hb : ∀ b ∈ Q.nbr a, fibOf x b = 0 := by
    intro b hbm
    refine fibOf_eq_zero (hx b ?_)
    rw [hnum a b hbm]
    exact ha
  rw [secHam_apply, fibOf_eq_zero (hx a ha), map_zero,
    Finset.sum_eq_zero (fun b hbm => by rw [hb b hbm]; simp),
    Finset.sum_eq_zero (fun b hbm => by rw [hb b hbm, map_zero, smul_zero])]
  simp

end QgFullNumber

/-- **Momentum conservation** for the rebuilt model: the bands are the momentum blocks. -/
theorem qgElimFull_momentum_conserving (W : WallPot) (g : ℝ) (num : Mom → ℕ)
    (x : secCore (ι := EGMode)) {n : ℕ}
    (hx : ∀ a : EGMode, num a.1 ≠ n → (x : Sec EGMode) a = 0) (a : EGMode) (ha : num a.1 ≠ n) :
    (secHam W (qgElimFullModes g) x : Sec EGMode) a = 0 :=
  secHam_number_conserving W (qgElimFullModes g)
    (num := fun a => num a.1) (fun _ _ hb => congrArg num (mem_eNbr.mp hb)) x hx a ha

/-- **Particle-number conservation** for the rebuilt model. -/
theorem qgElimFull_number_conserving (W : WallPot) (g : ℝ) {num : EGMode → ℕ}
    (hnum : ∀ a b : EGMode, b.1 = a.1 → num b = num a) (x : secCore (ι := EGMode)) {n : ℕ}
    (hx : ∀ a, num a ≠ n → (x : Sec EGMode) a = 0) (a : EGMode) (ha : num a ≠ n) :
    (secHam W (qgElimFullModes g) x : Sec EGMode) a = 0 :=
  secHam_number_conserving W (qgElimFullModes g)
    (fun a b hb => hnum a b (mem_eNbr.mp hb)) x hx a ha

/-! ## 8. Non-vacuity -/

/-- The mode set of the rebuilt model is still infinite: no lattice, no truncation. -/
theorem infinite_egmode : Infinite EGMode := inferInstance

/-- The eliminated torsion really is present, whenever the momentum is non-zero in that
direction. -/
theorem elimCoef_torsion_ne_zero (k : Mom) (hk : k 0 ≠ 0) :
    elimCoef k (torsionF 0 1 0) ((1, 0) : EComp) ≠ 0 := by
  have hne : ((1, 0) : EComp) ≠ (0, 0) := by simp [Prod.ext_iff]
  have h : elimCoef k (torsionF 0 1 0) ((1, 0) : EComp) = Complex.I * ((k 0 : ℤ) : ℂ) := by
    rw [elimCoef_torsion]
    simp [eind, hne]
  rw [h]
  simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, false_or]
  exact_mod_cast hk

/-- The 3D gauge fixing is really present on the eliminated components. -/
theorem elimCoef_gauge3d_ne_zero (k : Mom) (hk : k 0 ≠ 0) :
    elimCoef k (gauge3dF 0) ((0, 0) : EComp) ≠ 0 := by
  have h1 : ((0, 0) : EComp) ≠ (1, 0) := by simp [Prod.ext_iff]
  have h2 : ((0, 0) : EComp) ≠ (2, 0) := by simp [Prod.ext_iff, Fin.ext_iff]
  have h : elimCoef k (gauge3dF 0) ((0, 0) : EComp) = Complex.I * ((k 0 : ℤ) : ℂ) := by
    rw [elimCoef_gauge3d, Fin.sum_univ_three]
    simp [eind, h1, h2]
  rw [h]
  simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, false_or]
  exact_mod_cast hk

/-- The rebuilt quadratic form is not the zero form: its diagonal entry on a vielbein component is
positive at any non-zero momentum. -/
theorem conj_mul_self_ofReal (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  simpa using RCLike.conj_mul (K := ℂ) z

theorem eGram_diag_ne_zero (k : Mom) (hk : k 0 ≠ 0) :
    eGram ((k, (1, 0)) : EGMode) (k, (1, 0)) ≠ 0 := by
  have hsum : eGram ((k, (1, 0)) : EGMode) (k, (1, 0))
      = ((∑ F : FormIdx, ‖elimCoef k F ((1, 0) : EComp)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [eGram, if_true, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun F _ => conj_mul_self_ofReal _
  intro h0
  rw [hsum] at h0
  have hzero : (∑ F : FormIdx, ‖elimCoef k F ((1, 0) : EComp)‖ ^ 2) = 0 := by exact_mod_cast h0
  have hterm : ‖elimCoef k (torsionF 0 1 0) ((1, 0) : EComp)‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun F _ => by positivity)).mp hzero _
      (Finset.mem_univ _)
  refine elimCoef_torsion_ne_zero k hk (norm_eq_zero.mp ?_)
  nlinarith [norm_nonneg (elimCoef k (torsionF 0 1 0) ((1, 0) : EComp))]

/-- The scalaron–vielbein coupling is really present whenever the coupling constant is
non-zero. -/
theorem eCoupling_ne_zero (g : ℝ) (hg : g ≠ 0) (k : Mom) :
    eCoupling g ((k, (0, 0)) : EGMode) (k, (0, 0)) ≠ 0 := by
  simp only [eCoupling, eTrace]
  norm_num [hg]

end

end BookProof.QgFullEliminated


