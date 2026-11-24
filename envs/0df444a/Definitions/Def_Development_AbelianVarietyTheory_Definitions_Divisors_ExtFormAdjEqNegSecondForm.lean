-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:25.120351+00:00
-- url     : https://prove2.me/theorems/80e3bc26-7933-47c3-9ebb-8f982e7e59b9
-- title:
--   Ext Form Adj Eq Neg Second Form
-- statement:
--   Definitions and structural lemmas for Ext Form Adj Eq Neg Second Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_blockQS_eq
import Theorems.Thm_GlobalTheory_HermFrame_norm_form_le
import Theorems.Thm_GlobalTheory_HermFrame_norm_form_mulVec_le
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_IsPshC2On_add
import Theorems.Thm_GlobalTheory_IsPshC2On_mono
import Theorems.Thm_GlobalTheory_dbar_add
import Theorems.Thm_GlobalTheory_dbar_congr
import Theorems.Thm_GlobalTheory_dbar_mul
import Theorems.Thm_GlobalTheory_leviForm_log_normSq_add_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero


set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
namespace GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
def mdel (A : E → Matrix m n ℂ) (z ξ : E) : Matrix m n ℂ :=
  of fun a b => del (fun x => A x a b) z ξ
def mdbar (A : E → Matrix m n ℂ) (z η : E) : Matrix m n ℂ :=
  of fun a b => dbar (fun x => A x a b) z η
def mddbar (A : E → Matrix m n ℂ) (z ξ η : E) : Matrix m n ℂ :=
  of fun a b => ddbar (fun x => A x a b) z ξ η
def MContDiffAt (k : WithTop ℕ∞) (A : E → Matrix m n ℂ) (z : E) : Prop :=
  ∀ a b, ContDiffAt ℝ k (fun x => A x a b) z
section Calculus
variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}
@[simp] theorem mdel_apply (A : E → Matrix m n ℂ) (z ξ : E) (a : m) (b : n) :
    mdel A z ξ a b = del (fun x => A x a b) z ξ := rfl
@[simp] theorem mdbar_apply (A : E → Matrix m n ℂ) (z η : E) (a : m) (b : n) :
    mdbar A z η a b = dbar (fun x => A x a b) z η := rfl
@[simp] theorem mddbar_apply (A : E → Matrix m n ℂ) (z ξ η : E) (a : m) (b : n) :
    mddbar A z ξ η a b = ddbar (fun x => A x a b) z ξ η := rfl
theorem mdel_congr (h : A =ᶠ[𝓝 z] B) (ξ : E) : mdel A z ξ = mdel B z ξ := by
  ext a b
  rw [mdel_apply, mdel_apply, del_congr (h.mono fun x hx => congrFun (congrFun hx a) b)]
theorem mdbar_congr (h : A =ᶠ[𝓝 z] B) (ξ : E) : mdbar A z ξ = mdbar B z ξ := by
  ext a b
  rw [mdbar_apply, mdbar_apply, dbar_congr (h.mono fun x hx => congrFun (congrFun hx a) b)]
@[simp] theorem mdel_const (C : Matrix m n ℂ) (z ξ : E) : mdel (fun _ => C) z ξ = 0 := by
  ext a b; simp
@[simp] theorem mdbar_const (C : Matrix m n ℂ) (z ξ : E) : mdbar (fun _ => C) z ξ = 0 := by
  ext a b; simp
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.of_le (h : MContDiffAt k A z) (hjk : j ≤ k) : MContDiffAt j A z :=
  fun a b => (h a b).of_le hjk
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.diff (h : MContDiffAt 1 A z) (a : m) (b : n) :
    DifferentiableAt ℝ (fun x => A x a b) z := (h a b).differentiableAt one_ne_zero
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem mContDiffAt_const (C : Matrix m n ℂ) : MContDiffAt k (fun _ : E => C) z :=
  fun _ _ => contDiffAt_const
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.add (h : MContDiffAt k A z) (h' : MContDiffAt k B z) :
    MContDiffAt k (fun x => A x + B x) z := fun a b => (h a b).add (h' a b)
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.sub (h : MContDiffAt k A z) (h' : MContDiffAt k B z) :
    MContDiffAt k (fun x => A x - B x) z := fun a b => (h a b).sub (h' a b)
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.neg (h : MContDiffAt k A z) : MContDiffAt k (fun x => -A x) z :=
  fun a b => (h a b).neg
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.smul {f : E → ℂ} (hf : ContDiffAt ℝ k f z) (h : MContDiffAt k A z) :
    MContDiffAt k (fun x => f x • A x) z := fun a b => hf.mul (h a b)
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.transpose (h : MContDiffAt k A z) : MContDiffAt k (fun x => (A x)ᵀ) z :=
  fun a b => h b a
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.submatrix {m' n' : Type*} (h : MContDiffAt k A z) (f : m' → m) (g : n' → n) :
    MContDiffAt k (fun x => (A x).submatrix f g) z := fun a b => h (f a) (g b)
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.mul [Fintype n] {B : E → Matrix n l ℂ} (h : MContDiffAt k A z)
    (h' : MContDiffAt k B z) : MContDiffAt k (fun x => A x * B x) z := fun a b => by
  simp only [mul_apply]
  exact ContDiffAt.sum fun c _ => (h a c).mul (h' c b)
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.det [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ}
    (h : MContDiffAt k A z) : ContDiffAt ℝ k (fun x => (A x).det) z := by
  simp only [det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => h _ _)
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.inv [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ}
    (h : MContDiffAt k A z) (hu : IsUnit (A z).det) : MContDiffAt k (fun x => (A x)⁻¹) z := by
  intro a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]
  refine (h.det.inv hu.ne_zero).mul (MContDiffAt.det (A := fun x => (A x).updateRow b (Pi.single a 1))
    fun c d => ?_)
  simp only [updateRow_apply]
  split_ifs
  exacts [contDiffAt_const, h c d]
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.eventually_isUnit [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ}
    (h : MContDiffAt k A z) (hu : IsUnit (A z).det) : ∀ᶠ x in 𝓝 z, IsUnit (A x).det :=
  (h.det.continuousAt.eventually_ne hu.ne_zero).mono fun _ hx => hx.isUnit
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem MContDiffAt.eventually_two [Finite m] [Finite n] (h : MContDiffAt 2 A z) :
    ∀ᶠ x in 𝓝 z, MContDiffAt 2 A x :=
  eventually_all.2 fun a => eventually_all.2 fun b => (h a b).eventually (by simp)
theorem MContDiffAt.mdel (h : MContDiffAt k A z) (hjk : j + 1 ≤ k) (ξ : E) :
    MContDiffAt j (fun x => mdel A x ξ) z := fun a b => by
  have h1 := (h a b).fderiv_right hjk
  simp only [mdel_apply, del_apply]
  exact ((h1.clm_apply contDiffAt_const).sub
    ((h1.clm_apply contDiffAt_const).const_smul I)).const_smul (1 / 2 : ℂ)
theorem MContDiffAt.mdbar (h : MContDiffAt k A z) (hjk : j + 1 ≤ k) (η : E) :
    MContDiffAt j (fun x => mdbar A x η) z := fun a b => by
  have h1 := (h a b).fderiv_right hjk
  simp only [mdbar_apply, dbar_apply]
  exact ((h1.clm_apply contDiffAt_const).add
    ((h1.clm_apply contDiffAt_const).const_smul I)).const_smul (1 / 2 : ℂ)
theorem mdbar_add (h : MContDiffAt 1 A z) (h' : MContDiffAt 1 B z) (ξ : E) :
    mdbar (fun x => A x + B x) z ξ = mdbar A z ξ + mdbar B z ξ := by
  ext a b; simp [dbar_add (h.diff a b) (h'.diff a b)]
theorem mdel_smul {f : E → ℂ} (hf : DifferentiableAt ℝ f z) (h : MContDiffAt 1 A z) (ξ : E) :
    mdel (fun x => f x • A x) z ξ = f z • mdel A z ξ + del f z ξ • A z := by
  ext a b; simp [del_mul hf (h.diff a b)]
theorem mdbar_smul {f : E → ℂ} (hf : DifferentiableAt ℝ f z) (h : MContDiffAt 1 A z) (ξ : E) :
    mdbar (fun x => f x • A x) z ξ = f z • mdbar A z ξ + dbar f z ξ • A z := by
  ext a b; simp [dbar_mul hf (h.diff a b)]
end Calculus
section Frame
variable [Fintype n] [DecidableEq n]
structure IsHermFrame (U : Set E) (H : E → Matrix n n ℂ) : Prop where

  isOpen : IsOpen U

  smooth : ∀ a b, ContDiffOn ℝ ∞ (fun x => H x a b) U

  herm : ∀ z ∈ U, (H z).IsHermitian

  isUnit : ∀ z ∈ U, IsUnit (H z).det
structure IsPosFrame (U : Set E) (H : E → Matrix n n ℂ) : Prop where

  isOpen : IsOpen U

  smooth : ∀ a b, ContDiffOn ℝ ∞ (fun x => H x a b) U

  posDef : ∀ z ∈ U, (H z).PosDef
def conn (H : E → Matrix n n ℂ) (z ξ : E) : Matrix n n ℂ := (H z)ᵀ⁻¹ * (mdel H z ξ)ᵀ
def curv (H : E → Matrix n n ℂ) (z ξ η : E) : Matrix n n ℂ := -mdbar (fun x => conn H x ξ) z η
def covDel (H : E → Matrix n n ℂ) (s : E → n → ℂ) (z ξ : E) : n → ℂ :=
  (fun a => del (fun x => s x a) z ξ) + conn H z ξ *ᵥ s z
def dualGram (H : Matrix n n ℂ) : Matrix n n ℂ := H⁻¹ᵀ
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem IsPosFrame.isHermFrame (h : IsPosFrame U H) : IsHermFrame U H :=
  ⟨h.isOpen, h.smooth, fun z hz => (h.posDef z hz).isHermitian,
    fun z hz => (isUnit_iff_isUnit_det _).1 (h.posDef z hz).isUnit⟩
theorem conn_transpose_mul (hu : IsUnit (H z).det) (ξ : E) :
    (conn H z ξ)ᵀ * H z = mdel H z ξ := by
  rw [conn, transpose_mul, transpose_transpose, ← transpose_nonsing_inv, transpose_transpose,
    nonsing_inv_mul_cancel_right _ _ hu]
theorem eq_conn_of_compatible (hu : IsUnit (H z).det) {ξ : E} {T : Matrix n n ℂ}
    (h : Tᵀ * H z = mdel H z ξ) : T = conn H z ξ := by
  rw [conn, ← h, transpose_mul, transpose_transpose,
    nonsing_inv_mul_cancel_left _ _ (by rwa [det_transpose])]
theorem conn_congr (h : H =ᶠ[𝓝 z] H') (ξ : E) : conn H z ξ = conn H' z ξ := by
  rw [conn, conn, mdel_congr h, h.self_of_nhds]
theorem curv_congr (h : H =ᶠ[𝓝 z] H') (ξ η : E) : curv H z ξ η = curv H' z ξ η := by
  rw [curv, curv, mdbar_congr (h.eventuallyEq_nhds.mono fun x hx => conn_congr hx ξ)]
theorem MContDiffAt.conn (h : MContDiffAt k H z) (hu : IsUnit (H z).det) (hjk : j + 1 ≤ k)
    (ξ : E) : MContDiffAt j (fun x => conn H x ξ) z :=
  ((h.of_le (le_self_add.trans hjk)).transpose.inv (by rwa [det_transpose])).mul
    (h.mdel hjk ξ).transpose
theorem MContDiffAt.curv (h : MContDiffAt k H z) (hu : IsUnit (H z).det) (hjk : j + 2 ≤ k)
    (ξ η : E) : MContDiffAt j (fun x => curv H x ξ η) z :=
  ((h.conn hu (j := j + 1) (by rwa [add_assoc, one_add_one_eq_two]) ξ).mdbar le_rfl η).neg
@[simp] theorem conn_const (C : Matrix n n ℂ) (z ξ : E) : conn (fun _ => C) z ξ = 0 := by
  simp [conn]
@[simp] theorem curv_const (C : Matrix n n ℂ) (z ξ η : E) : curv (fun _ => C) z ξ η = 0 := by
  simp [curv]
theorem conn_smul {f : E → ℝ} (hf : DifferentiableAt ℝ f z) (hf0 : f z ≠ 0)
    (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    conn (fun x => (f x : ℂ) • H x) z ξ =
      conn H z ξ + del (fun x => (Real.log (f x) : ℂ)) z ξ • (1 : Matrix n n ℂ) := by
  have hf0' : (f z : ℂ) ≠ 0 := by exact_mod_cast hf0
  refine (eq_conn_of_compatible ?_ ?_).symm
  · rw [det_smul]; exact (pow_ne_zero _ hf0').isUnit.mul hu
  · rw [mdel_smul (f := fun x => (f x : ℂ)) (ofRealCLM.differentiableAt.comp z hf) h,
      del_ofReal_comp (Real.hasDerivAt_log hf0) hf, ← conn_transpose_mul hu]
    simp only [transpose_add, transpose_smul, transpose_one, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul]
    congr 2
    push_cast; field_simp
theorem curv_smul {f : E → ℝ} (hf : ContDiffAt ℝ 2 f z) (hf0 : f z ≠ 0)
    (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    curv (fun x => (f x : ℂ) • H x) z ξ η =
      curv H z ξ η - leviForm (fun x => Real.log (f x)) z ξ η • (1 : Matrix n n ℂ) := by
  have hl : ContDiffAt ℝ 2 (fun x => (Real.log (f x) : ℂ)) z := contDiffAt_ofReal_comp (hf.log hf0)
  have hl' : MContDiffAt 2 (fun x => (of fun _ _ => (Real.log (f x) : ℂ) : Matrix Unit Unit ℂ)) z :=
    fun _ _ => hl
  have hd : ContDiffAt ℝ 1 (fun x => del (fun x => (Real.log (f x) : ℂ)) x ξ) z :=
    hl'.mdel (by norm_num) ξ () ()
  have he : (fun x => conn (fun x => (f x : ℂ) • H x) x ξ) =ᶠ[𝓝 z] fun x =>
      conn H x ξ + del (fun x => (Real.log (f x) : ℂ)) x ξ • (1 : Matrix n n ℂ) := by
    filter_upwards [hf.eventually (by simp), hf.continuousAt.eventually_ne hf0, h.eventually_two,
      h.eventually_isUnit hu] with x h1 h2 h3 h4
    exact conn_smul (h1.differentiableAt two_ne_zero) h2 (h3.of_le one_le_two) h4 ξ
  rw [curv, mdbar_congr he, mdbar_add (h.conn hu (by norm_num) ξ)
    (MContDiffAt.smul hd (mContDiffAt_const _)),
    mdbar_smul (hd.differentiableAt one_ne_zero) (mContDiffAt_const _), mdbar_const, leviForm,
    ddbar_eq_dbar_del hl, curv]
  simp only [smul_zero, zero_add, neg_add, sub_eq_add_neg]
theorem curv_line [Unique n] {f : E → ℝ} (hf : ContDiffAt ℝ 2 f z) (hf0 : f z ≠ 0)
    (hH : ∀ᶠ x in 𝓝 z, H x default default = f x) (ξ η : E) (a b : n) :
    curv H z ξ η a b = -leviForm (fun x => Real.log (f x)) z ξ η := by
  have he : H =ᶠ[𝓝 z] fun x => (f x : ℂ) • (1 : Matrix n n ℂ) := hH.mono fun x hx => by
    ext a b; rw [Subsingleton.elim a default, Subsingleton.elim b default, hx]; simp
  rw [curv_congr he, curv_smul hf hf0 (mContDiffAt_const _) (by simp), Subsingleton.elim a b]
  simp
section Pullback
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E'] {φ : E' → E} {w : E'}
end Pullback
end Frame
def kappa : ℂ := I / (2 * Real.pi)
def ddc (u : E → ℝ) (z ξ η : E) : ℂ := kappa * leviForm u z ξ η
def diagVal {V : Type*} (α : V → V → ℂ) (ξ : V) : ℝ := (-I * α ξ ξ).re
def FormLe {V : Type*} (α β : V → V → ℂ) : Prop := ∀ ξ, diagVal α ξ ≤ diagVal β ξ
def FormAbsLe {V : Type*} (α : V → V → ℂ) (C : ℝ) (β : V → V → ℂ) : Prop :=
  FormLe (fun ξ η => -C * β ξ η) α ∧ FormLe α fun ξ η => C * β ξ η
section Tangent
variable {ι : Type*} [Fintype ι]
def formOf (G : Matrix ι ι ℂ) (ξ η : ι → ℂ) : ℂ := I * form G ξ η
variable [Fintype n]
def OneFormBound (U : Set (ι → ℂ)) (H : (ι → ℂ) → Matrix n n ℂ) (G : (ι → ℂ) → Matrix ι ι ℂ)
    (A : (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ) (C : ℝ) : Prop :=
  ∀ z ∈ U, (H z).PosDef ∧ (G z).PosSemidef ∧
    ∀ ξ, opNorm (H z) (H z) (A z ξ) ≤ C * gnorm (G z) ξ
def TwoFormBound (U : Set (ι → ℂ)) (H : (ι → ℂ) → Matrix n n ℂ) (G : (ι → ℂ) → Matrix ι ι ℂ)
    (F : (ι → ℂ) → (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ) (C : ℝ) : Prop :=
  ∀ z ∈ U, (H z).PosDef ∧ (G z).PosSemidef ∧
    ∀ ξ η, opNorm (H z) (H z) (F z ξ η) ≤ C * gnorm (G z) ξ * gnorm (G z) η
variable {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix n n ℂ} {G : (ι → ℂ) → Matrix ι ι ℂ} {C C' : ℝ}
theorem TwoFormBound.norm_form_le {F : (ι → ℂ) → (ι → ℂ) → (ι → ℂ) → Matrix n n ℂ}
    (h : TwoFormBound U H G F C) {z : ι → ℂ} (hz : z ∈ U) (ξ : ι → ℂ) (v : n → ℂ) :
    ‖form (H z) (F z ξ ξ *ᵥ v) v‖ ≤ C * gnorm (G z) ξ ^ 2 * gnorm (H z) v ^ 2 :=
  (norm_form_mulVec_le (h z hz).1 _ v).trans (mul_le_mul_of_nonneg_right
    (((h z hz).2.2 ξ ξ).trans_eq (by ring)) (sq_nonneg _))
end Tangent
def wedge {V : Type*} (α β : V → V → ℂ) (ξ₁ η₁ ξ₂ η₂ : V) : ℂ :=
  α ξ₁ η₁ * β ξ₂ η₂ + α ξ₂ η₂ * β ξ₁ η₁ - α ξ₁ η₂ * β ξ₂ η₁ - α ξ₂ η₁ * β ξ₁ η₂
def ddcForm (α : E → E → E → ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  kappa * (ddbar (fun x => α x ξ₂ η₂) z ξ₁ η₁ + ddbar (fun x => α x ξ₁ η₁) z ξ₂ η₂
    - ddbar (fun x => α x ξ₂ η₁) z ξ₁ η₂ - ddbar (fun x => α x ξ₁ η₂) z ξ₂ η₁)
section Chern
variable [Fintype n] [DecidableEq n]
def chernOne (H : E → Matrix n n ℂ) (z ξ η : E) : ℂ := kappa * (curv H z ξ η).trace
def curvMinor (H : E → Matrix n n ℂ) (z : E) (a b : n) (ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  wedge (fun ξ η => curv H z ξ η a a) (fun ξ η => curv H z ξ η b b) ξ₁ η₁ ξ₂ η₂
    - wedge (fun ξ η => curv H z ξ η a b) (fun ξ η => curv H z ξ η b a) ξ₁ η₁ ξ₂ η₂
def chernTwo (H : E → Matrix n n ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  kappa ^ 2 * (1 / 2 * ∑ a, ∑ b, curvMinor H z a b ξ₁ η₁ ξ₂ η₂)
def chTwo (H : E → Matrix n n ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) : ℂ :=
  kappa ^ 2 / 2 *
    ∑ a, ∑ b, wedge (fun ξ η => curv H z ξ η a b) (fun ξ η => curv H z ξ η b a) ξ₁ η₁ ξ₂ η₂
def lineCurv (H : E → Matrix n n ℂ) (z : E) (w : n → ℂ) (ξ η : E) : ℂ :=
  kappa * (form (H z) (curv H z ξ η *ᵥ w) w / form (H z) w w)
end Chern
section Sub
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
def secondForm (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) : Matrix l m ℂ :=
  blockQS (conn H z ξ)
def secondFormAdj (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) : Matrix m l ℂ :=
  adj (subGram (H z)) (quotGram (H z)) (secondForm H z η)
def extForm (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) : Matrix m l ℂ :=
  orthProj (H z) * mdbar (fun x => orthLift (H x)) z η
def extFormAdj (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) : Matrix l m ℂ :=
  adj (quotGram (H z)) (subGram (H z)) (extForm H z ξ)
def extTrace (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ η : E) : ℂ :=
  kappa * (extFormAdj H z ξ * extForm H z η).trace
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype m] [Fintype l] [DecidableEq m]
  [DecidableEq l] in

theorem MContDiffAt.subGram (h : MContDiffAt k H z) : MContDiffAt k (fun x => subGram (H x)) z :=
  h.submatrix Sum.inl Sum.inl
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype l] [DecidableEq l] in

theorem MContDiffAt.quotGram (h : MContDiffAt k H z) (hu : IsUnit (HermFrame.subGram (H z)).det) :
    MContDiffAt k (fun x => quotGram (H x)) z :=
  (h.submatrix Sum.inr Sum.inr).sub (((h.submatrix Sum.inr Sum.inl).mul (h.subGram.inv hu)).mul
    (h.submatrix Sum.inl Sum.inr))
theorem secondForm_eq (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : E) :
    secondForm H z ξ = (conn H z ξ).toBlocks₂₁ := blockQS_eq _
def firstSecondForm {N j : ℕ} (hj : j ≤ N) (K : E → Matrix (Fin N) (Fin N) ℂ) (z ξ : E) :
    Matrix (Fin (N - j)) (Fin j) ℂ := secondForm (fun x => adapt hj (K x)) z ξ
end Sub
section Examples
def tautGram (e : ℕ) (z : Fin e → ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  of fun _ _ => ((1 + ∑ k, ‖z k‖ ^ 2 : ℝ) : ℂ)
theorem contDiff_one_add_normSq (e : ℕ) :
    ContDiff ℝ ∞ fun z : Fin e → ℂ => 1 + ∑ k, ‖z k‖ ^ 2 :=
  contDiff_const.add (ContDiff.sum fun k _ => (contDiff_apply ℝ ℂ k).norm_sq ℂ)
theorem isPosFrame_tautGram (e : ℕ) : IsPosFrame Set.univ (tautGram e) := by
  refine ⟨isOpen_univ, fun _ _ =>
    (ofRealCLM.contDiff.comp (contDiff_one_add_normSq e)).contDiffOn, fun z _ => ?_⟩
  have : tautGram e z = diagonal fun _ => ((1 + ∑ k, ‖z k‖ ^ 2 : ℝ) : ℂ) := by
    ext a b; rw [Subsingleton.elim a b]; simp [tautGram]
  rw [this, posDef_diagonal_iff]
  intro _
  exact_mod_cast (by positivity : (0 : ℝ) < 1 + ∑ k, ‖z k‖ ^ 2)
theorem curv_tautGram_zero (e : ℕ) (ξ η : Fin e → ℂ) :
    curv (tautGram e) 0 ξ η = -(∑ k, ξ k * conj (η k)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  rw [curv_line (f := fun z : Fin e → ℂ => 1 + ∑ k, ‖z k‖ ^ 2)
    ((contDiff_one_add_normSq e).contDiffAt.of_le (by norm_cast)) (by simp)
    (Eventually.of_forall fun _ => rfl), Subsingleton.elim a b]
  let φ : (Fin e → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin e) := (EuclideanSpace.equiv (Fin e) ℂ).symm
  have h : (fun x : Fin e → ℂ => Real.log (1 + ∑ k, ‖x k‖ ^ 2)) =
      fun x => Real.log (‖φ x‖ ^ 2 + 1) := by
    funext x; rw [EuclideanSpace.norm_sq_eq, add_comm]; rfl
  rw [h, leviForm_log_normSq_add_comp φ.contDiff.contDiffAt (by simp), φ.fderiv]
  simp [φ, PiLp.inner_apply]
example (ξ : Fin 1 → ℂ) :
    diagVal (chernOne (tautGram 1) 0) ξ = -‖ξ 0‖ ^ 2 / (2 * Real.pi) := by
  have : -I * chernOne (tautGram 1) 0 ξ ξ = ((-‖ξ 0‖ ^ 2 / (2 * Real.pi) : ℝ) : ℂ) := by
    simp only [chernOne, curv_tautGram_zero, kappa, Fin.sum_univ_one, mul_conj', trace_smul,
      trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    linear_combination ((‖ξ 0‖ : ℂ) ^ 2 / (2 * Real.pi)) * I_mul_I
  rw [diagVal, this, ofReal_re]
example : ¬ TwoFormBound {0} (tautGram 1) (fun _ => 1) (curv (tautGram 1)) 0 := fun h => by
  have := h.norm_form_le rfl (fun _ => 1) fun _ => 1
  simp [curv_tautGram_zero, form_eq_sum, tautGram, neg_mulVec] at this
  exact absurd this (by norm_num)
example : IsHermFrame Set.univ (fun z => -tautGram 1 z) ∧
    ¬ IsPosFrame Set.univ (fun z => -tautGram 1 z) := by
  have h := (isPosFrame_tautGram 1).isHermFrame
  refine ⟨⟨isOpen_univ, fun a b => (h.smooth a b).neg, fun z hz => (h.herm z hz).neg,
    fun z hz => ?_⟩, fun h' => ?_⟩
  · rw [det_neg]; exact (isUnit_one.neg.pow _).mul (h.isUnit z hz)
  · have := (h'.posDef 0 trivial).diag_pos (i := 0)
    simp [tautGram] at this
    exact absurd this (by norm_num)
def tautPairGram (z : ℂ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks (of fun _ _ => 1 + z * conj z) (of fun _ _ => z) (of fun _ _ => conj z) 1
example (ξ : ℂ) : secondForm tautPairGram 0 ξ () () = ξ := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
  change del (fun x : ℂ => x) 0 ξ = ξ
  rw [del_eq_fderiv differentiableAt_fun_id]; simp
end Examples
end GlobalTheory.HermFrame


