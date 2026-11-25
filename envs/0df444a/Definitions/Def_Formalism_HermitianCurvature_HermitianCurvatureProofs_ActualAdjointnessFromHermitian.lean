-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:31.097708+00:00
-- url     : https://prove2.me/theorems/5d54ed5f-61bb-4eb2-abd8-1f90c8fbc178
-- title:
--   Actual Adjointness From Hermitian
-- statement:
--   Definitions and structural lemmas for Actual Adjointness From Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_eh
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_isOpen_OmX
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_uh_inv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_hi
import Theorems.Thm_Formalism_QuantumDeterminants_WRPres_coord_contDiff
import Theorems.Thm_Formalism_QuantumDeterminants_isOpen_OmX
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Gen
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
def partialFDerivFst (F : X × Y → E) (x : X × Y) : X →L[ℝ] E := (fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ X Y)
theorem hasFDerivAt_partial_fst {F : X × Y → E} {U : Set (X × Y)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {x : X × Y}
    (hx : x ∈ U) : HasFDerivAt (fun c' => F (c', x.2)) (partialFDerivFst F x) x.1 := by
  have h1 : DifferentiableAt ℝ F x := (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have h2 : HasFDerivAt (fun c' : X => (c', x.2)) (ContinuousLinearMap.inl ℝ X Y) x.1 :=
    hasFDerivAt_prodMk_left x.1 x.2
  exact HasFDerivAt.comp (g := F) x.1 h1.hasFDerivAt h2
theorem contDiffOn_partial_fderiv_fst {F : X × Y → E} {U : Set (X × Y)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (v : X) :
    ContDiffOn ℝ ∞ (fun x => partialFDerivFst F x v) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const
theorem eventually_slice {U : Set (X × Y)} (hU : IsOpen U) {x : X × Y} (hx : x ∈ U) :
    ∀ᶠ c' in nhds x.1, (c', x.2) ∈ U := by
  have hc : Continuous (fun c' : X => (c', x.2)) := by fun_prop
  exact hc.continuousAt.eventually (hU.mem_nhds hx)
end Gen
section Rad
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
theorem isOpen_OmX (m : ℕ) : IsOpen (OmX m) := by
  have : OmX m = ⋂ l : Fin m, {x : Fin m → ℂ | x l ≠ 0} := by
    ext x; simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
def zetaLin (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) : Mx k r →ₗ[ℂ] ℂ where
  toFun := zetaL k r z z' i
  map_add' a b := by simp [zetaL, herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  map_smul' a b := by simp [zetaL, herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]
theorem zetaL_contDiff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) :
    ContDiff ℝ ∞ (zetaL k r z z' i) :=
  ((LinearMap.toContinuousLinearMap (zetaLin k r z z' i)).contDiff (n := ∞)).restrict_scalars ℝ
theorem GGl_cast (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (GGl k r z z' g : ℂ) = zetaL k r z z' (Fin.last r) g * star (zetaL k r z z' (Fin.last r) g) -
      ((Tz k r z * Tz k r z' : ℝ) : ℂ) := by
  unfold GGl
  rw [Complex.ofReal_sub, Complex.star_def, Complex.mul_conj]
theorem GGl_continuous (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (GGl k r z z') := by
  unfold GGl
  exact (Complex.continuous_normSq.comp (zetaL_contDiff k r z z' (Fin.last r)).continuous).sub continuous_const
def OpR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × Mx k r) :=
  {x | x.1 ∈ OmX r ∧ 0 < GGl k r z z' x.2}
theorem isOpen_OpR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (OpR k r z z') :=
  ((isOpen_OmX r).preimage continuous_fst).inter
    (isOpen_lt continuous_const ((GGl_continuous k r z z').comp continuous_snd))
theorem DomR_sub_OpR : DomR k r z z' ⊆ OpR k r z z' := fun _ hx => ⟨hx.1, hx.2.2⟩
theorem mem_DomR_of_OpR {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ OpR k r z z') (hg : x.2 ∈ Glev k r (Fin.last r)) :
    x ∈ DomR k r z z' := ⟨hx.1, hg, hx.2⟩
theorem slice_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {Φ : Fn k r E}
    {U : Set ((Fin r → ℂ) × Mx k r)} {F : (Fin r → ℂ) × Mx k r → E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hΦ : ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x) {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ U)
    (hg : x.2 ∈ Glev k r i) : HasFDerivAt (fun c' => Φ c' x.2) (partialFDerivFst F x) x.1 := by
  refine (hasFDerivAt_partial_fst hU hF hx).congr_of_eventuallyEq ?_
  filter_upwards [eventually_slice hU hx] with c' hc'
  exact hΦ (c', x.2) hc' hg
theorem slice_zero {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {g : Mx k r}
    (hg : ¬ (g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g)) : (fun c' => Φ c' g) = fun _ => 0 := by
  funext c'
  exact hΦ.1 (c', g) fun h => hg h.2
theorem slice_diff {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (g : Mx k r) : DifferentiableAt ℝ (fun c' => Φ c' g) c := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 (c, g) ⟨hc, hg⟩
    exact (slice_hasFDerivAt hU hF hΦF hxU hg.1).differentiableAt
  · rw [slice_zero hΦ hg]
    exact differentiableAt_const _
open Classical in

def dirD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : Fin r → ℂ) (Φ : Fn k r E) : Fn k r E :=
  fun c g => if c ∈ OmX r then fderiv ℝ (fun c' => Φ c' g) c v else 0
def sandCLM (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B)
theorem dirD_mem (v : Fin r → ℂ) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    dirD v Φ ∈ RadSp k r z z' π π' := by
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · unfold dirD
    split_ifs with hc
    · have hg : ¬ (x.2 ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' x.2) := fun h => hx ⟨hc, h⟩
      rw [slice_zero hΦ hg]
      simp
    · rfl
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 x₀ hx₀
    refine ⟨U ∩ {x | x.1 ∈ OmX r}, fun x => partialFDerivFst F x v, hU.inter ((isOpen_OmX r).preimage continuous_fst),
      ⟨hxU, hx₀.1⟩, ?_, fun x hx hg => ?_⟩
    · exact (contDiffOn_partial_fderiv_fst hU hF v).mono Set.inter_subset_left
    · unfold dirD
      rw [if_pos (show x.1 ∈ OmX r from hx.2), (slice_hasFDerivAt hU hF hΦF hx.1 hg).fderiv]
  · unfold dirD
    rw [if_pos hx.1, if_pos hx.1]
    have he : (fun c' => Φ c' (h * x.2 * h')) =ᶠ[nhds x.1] fun c' => sandCLM (π h) (π' h') (Φ c' x.2) := by
      filter_upwards [(isOpen_OmX r).mem_nhds hx.1] with c' hc'
      exact hΦ.2.2 (c', x.2) ⟨hc', hx.2⟩ h hh h' hh'
    rw [he.fderiv_eq]
    have hd := (slice_diff hΦ hx.1 x.2).hasFDerivAt
    have := (((sandCLM (π h) (π' h')).restrictScalars ℝ).hasFDerivAt.comp x.1 hd).fderiv
    have h2 : (fun c' => sandCLM (π h) (π' h') (Φ c' x.2)) =
        (⇑((sandCLM (π h) (π' h')).restrictScalars ℝ) ∘ fun c' => Φ c' x.2) := rfl
    rw [h2, this]
    rfl
theorem dirD_lin (v : Fin r → ℂ) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π')
    (hΨ : Ψ ∈ RadSp k r z z' π π') (s : ℂ) : dirD v (Φ + s • Ψ) = dirD v Φ + s • dirD v Ψ := by
  funext c g
  simp only [dirD, Pi.add_apply, Pi.smul_apply]
  split_ifs with hc
  · have h1 := (slice_diff hΦ hc g).hasFDerivAt
    have h2 := (slice_diff hΨ hc g).hasFDerivAt
    have h3 := (h1.add (h2.const_smul s)).fderiv
    have h4 : (fun c' => Φ c' g + s • Ψ c' g) = ((fun c' => Φ c' g) + s • fun c' => Ψ c' g) := rfl
    rw [h4, h3]
    rfl
  · simp
theorem smul_mem {a : (Fin r → ℂ) × Mx k r → ℂ} (ha : ContDiffOn ℝ ∞ a (OpR k r z z'))
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', a (x.1, h * x.2 * h') = a x)
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    (fun c g => a (c, g) • Φ c g) ∈ RadSp k r z z' π π' := by
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · simp [hΦ.1 x hx]
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 x₀ hx₀
    refine ⟨U ∩ OpR k r z z', fun x => a x • F x, hU.inter (isOpen_OpR k r z z'), ⟨hxU, DomR_sub_OpR hx₀⟩,
      (ha.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hg => ?_⟩
    simp [hΦF x hx.1 hg]
  · simp only
    rw [hinv x hx h hh h' hh', hΦ.2.2 x hx h hh h' hh']
    ext w
    simp
end Rad
section Rad2
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
theorem herm_UH {ι : Type*} [Fintype ι] [DecidableEq ι] {H g : Matrix ι ι ℂ} (hg : g ∈ UH H) (x w : ι → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ w) = herm H x w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']
theorem fvec_last (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]
theorem UH_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {H a b : Matrix ι ι ℂ} (ha : a ∈ UH H) (hb : b ∈ UH H) :
    a * b ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  change (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']
theorem Glev_mul {i : Fin (r + 1)} {a b : Mx k r} (ha : a ∈ Glev k r i) (hb : b ∈ Glev k r i) :
    a * b ∈ Glev k r i := by
  refine ⟨UH_mul ha.1 hb.1, fun l hl => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hb.2 l hl).1, (hb.2 l hl).2]
  exact ha.2 l hl
theorem UW_Glev {h : Mx k r} (hh : h ∈ UWset k r z) (i : Fin (r + 1)) : h ∈ Glev k r i :=
  ⟨hh.1, fun a _ => hh.2.1 a⟩
theorem zeta_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (g : Mx k r) :
    zetaL k r z z' (Fin.last r) (h * g * h') = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  rw [fvec_last, fvec_last, ← Matrix.mulVec_mulVec, hh'.2.2, ← Matrix.mulVec_mulVec]
  conv_lhs => rw [← hh.2.2]
  exact herm_UH hh.1 _ _
theorem GG_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (g : Mx k r) :
    GGl k r z z' (h * g * h') = GGl k r z z' g := by
  unfold GGl
  rw [zeta_inv hh hh']
theorem DomR_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') {x : (Fin r → ℂ) × Mx k r}
    (hx : x ∈ DomR k r z z') : (x.1, h * x.2 * h') ∈ DomR k r z z' :=
  ⟨hx.1, Glev_mul (Glev_mul (UW_Glev hh _) hx.2.1) (UW_Glev hh' _), by
    change 0 < GGl k r z z' (h * x.2 * h'); rw [GG_inv hh hh']; exact hx.2.2⟩
theorem zeta_ne (hT : 0 ≤ Tz k r z * Tz k r z') {g : Mx k r} (hg : 0 < GGl k r z z' g) :
    zetaL k r z z' (Fin.last r) g ≠ 0 := by
  intro h0
  unfold GGl at hg
  rw [h0] at hg
  simp at hg
  linarith
theorem crd_p (l : Fin r) (Φ : Fn k r (Wq →L[ℂ] Wp)) :
    crd (pOp l) Φ = fun c g => c l • ((1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ - Complex.I • dirD (Pi.single l Complex.I) Φ)) c g := by
  funext c g
  simp only [crd, pOp, wirt, dirD, Pi.smul_apply, Pi.sub_apply]
  split_ifs <;> simp
theorem crd_pb (l : Fin r) (Φ : Fn k r (Wq →L[ℂ] Wp)) :
    crd (pbOp l) Φ = fun c g => star (c l) • ((1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ + Complex.I • dirD (Pi.single l Complex.I) Φ)) c g := by
  funext c g
  simp only [crd, pbOp, wirtBar, dirD, Pi.smul_apply, Pi.add_apply]
  split_ifs <;> simp
theorem coord_contDiff (l : Fin r) : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l) :=
  (contDiff_apply ℝ ℂ l).comp contDiff_fst
theorem star_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → ℂ} {s : Set X}
    (hf : ContDiffOn ℝ ∞ f s) : ContDiffOn ℝ ∞ (fun x => star (f x)) s :=
  Complex.conjCLE.contDiff.comp_contDiffOn hf
theorem cmul_mem (l : Fin r) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    (fun c g => c l • Φ c g) ∈ RadSp k r z z' π π' ∧ (fun c g => (c l)⁻¹ • Φ c g) ∈ RadSp k r z z' π π' ∧
    (fun c g => star (c l) • Φ c g) ∈ RadSp k r z z' π π' ∧
    (fun c g => (star (c l))⁻¹ • Φ c g) ∈ RadSp k r z z' π π' := by
  have h0 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l) (OpR k r z z') := (coord_contDiff l).contDiffOn
  have hne : ∀ x ∈ OpR k r z z', x.1 l ≠ 0 := fun x hx => hx.1 l
  refine ⟨smul_mem (a := fun x => x.1 l) h0 (fun _ _ _ _ _ _ => rfl) hΦ,
    smul_mem (a := fun x => (x.1 l)⁻¹) (h0.inv hne) (fun _ _ _ _ _ _ => rfl) hΦ,
    smul_mem (a := fun x => star (x.1 l)) (star_contDiff h0) (fun _ _ _ _ _ _ => rfl) hΦ,
    smul_mem (a := fun x => (star (x.1 l))⁻¹) ((star_contDiff h0).inv fun x hx => by simpa using hne x hx)
      (fun _ _ _ _ _ _ => rfl) hΦ⟩
theorem crd_mem (l : Fin r) (j : Fin 6) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    crd (opL l j) Φ ∈ RadSp k r z z' π π' := by
  have h1 : dirD (Pi.single l 1) Φ ∈ RadSp k r z z' π π' := dirD_mem _ hΦ
  have h2 : Complex.I • dirD (Pi.single l Complex.I) Φ ∈ RadSp k r z z' π π' :=
    (RadSp k r z z' π π').smul_mem _ (dirD_mem _ hΦ)
  fin_cases j
  · change crd (pOp l) Φ ∈ _
    rw [crd_p]
    have h3 : (1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ - Complex.I • dirD (Pi.single l Complex.I) Φ) ∈
        RadSp k r z z' π π' := (RadSp k r z z' π π').smul_mem _ ((RadSp k r z z' π π').sub_mem h1 h2)
    exact (cmul_mem l h3).1
  · exact (cmul_mem l hΦ).1
  · exact (cmul_mem l hΦ).2.1
  · change crd (pbOp l) Φ ∈ _
    rw [crd_pb]
    have h3 : (1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ + Complex.I • dirD (Pi.single l Complex.I) Φ) ∈
        RadSp k r z z' π π' := (RadSp k r z z' π π').smul_mem _ ((RadSp k r z z' π π').add_mem h1 h2)
    exact (cmul_mem l h3).2.2.1
  · exact (cmul_mem l hΦ).2.2.1
  · exact (cmul_mem l hΦ).2.2.2
theorem crd_lin (l : Fin r) (j : Fin 6) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π')
    (hΨ : Ψ ∈ RadSp k r z z' π π') (s : ℂ) :
    crd (opL l j) (Φ + s • Ψ) = crd (opL l j) Φ + s • crd (opL l j) Ψ := by
  fin_cases j
  · change crd (pOp l) _ = crd (pOp l) _ + s • crd (pOp l) _
    rw [crd_p, crd_p, crd_p, dirD_lin _ hΦ hΨ, dirD_lin _ hΦ hΨ]
    funext c g
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_add, smul_sub, smul_smul]
    module
  · funext c g
    change c l • (Φ c g + s • Ψ c g) = c l • Φ c g + s • (c l • Ψ c g)
    module
  · funext c g
    change (c l)⁻¹ • (Φ c g + s • Ψ c g) = (c l)⁻¹ • Φ c g + s • ((c l)⁻¹ • Ψ c g)
    module
  · change crd (pbOp l) _ = crd (pbOp l) _ + s • crd (pbOp l) _
    rw [crd_pb, crd_pb, crd_pb, dirD_lin _ hΦ hΨ, dirD_lin _ hΦ hΨ]
    funext c g
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
    module
  · funext c g
    change star (c l) • (Φ c g + s • Ψ c g) = star (c l) • Φ c g + s • (star (c l) • Ψ c g)
    module
  · funext c g
    change (star (c l))⁻¹ • (Φ c g + s • Ψ c g) = (star (c l))⁻¹ • Φ c g + s • ((star (c l))⁻¹ • Ψ c g)
    module
theorem fnVal_contDiffOn (hT : 0 ≤ Tz k r z * Tz k r z') (j : Fin 6) :
    ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fnVal k r z z' j x.2) (OpR k r z z') := by
  have h0 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zetaL k r z z' (Fin.last r) x.2) (OpR k r z z') :=
    ((zetaL_contDiff k r z z' (Fin.last r)).comp contDiff_snd).contDiffOn
  have hne : ∀ x ∈ OpR k r z z', zetaL k r z z' (Fin.last r) x.2 ≠ 0 := fun x hx => zeta_ne hT hx.2
  have h4 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => (GGl k r z z' x.2 : ℂ)) (OpR k r z z') := by
    simp only [GGl_cast]
    exact (h0.mul (star_contDiff h0)).sub contDiffOn_const
  fin_cases j
  · exact h0
  · exact h0.inv hne
  · exact star_contDiff h0
  · exact (star_contDiff h0).inv fun x hx => by simpa using hne x hx
  · exact h4
  · exact h4.inv fun x hx => by
      have : (0 : ℝ) < GGl k r z z' x.2 := hx.2
      exact_mod_cast this.ne'
theorem fnVal_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (j : Fin 6) (g : Mx k r) :
    fnVal k r z z' j (h * g * h') = fnVal k r z z' j g := by
  fin_cases j <;> simp only [fnVal, zeta_inv hh hh', GG_inv hh hh']
theorem fn_mem (hT : 0 ≤ Tz k r z * Tz k r z') (j : Fin 6) {Φ : Fn k r (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k r z z' π π') : (fun c g => fnVal k r z z' j g • Φ c g) ∈ RadSp k r z z' π π' :=
  smul_mem (a := fun x => fnVal k r z z' j x.2) (fnVal_contDiffOn hT j)
    (fun _ _ _ hh _ hh' => fnVal_inv hh hh' j _) hΦ
end Rad2
section Geo
theorem herm_bvec_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (p : Fin m) :
    herm H v (bvec p) = (H *ᵥ v) p := by
  simp [herm, bvec, dotProduct, Pi.single_apply]
theorem Hpk_mulVec (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = GBasic.sgn k r p * v (GBasic.sig k r p) := by
  simp [mulVec, dotProduct, GBasic.Hpk_eq]
theorem mulVec_bvec {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (g *ᵥ bvec j) i = g i j := by
  simp [mulVec, dotProduct, bvec, Pi.single_apply]
theorem Nlev_last {k r : ℕ} {n : Mx k r} (hn : n ∈ Nlev k r (Fin.last r)) : n = 1 := by
  obtain ⟨⟨hU, -, h3⟩, -, hfix⟩ := hn
  ext i j
  by_cases hj1 : j.val < r
  · have h := (hfix ⟨j.val, hj1⟩ (by simpa using hj1)).1
    have e : eI k r ⟨j.val, hj1⟩ = j := Fin.ext rfl
    rw [e] at h
    have := congrFun h i
    rw [mulVec_bvec] at this
    rw [this, Matrix.one_apply, bvec, Pi.single_apply]
  by_cases hj2 : r + k < j.val
  · have hjl := j.isLt
    have ha : 2 * r + k - j.val < r := by omega
    have h := (hfix ⟨2 * r + k - j.val, ha⟩ (by simpa using ha)).2
    have e : esI k r ⟨2 * r + k - j.val, ha⟩ = j := Fin.ext (by simp only [esI]; omega)
    rw [e] at h
    have := congrFun h i
    rw [mulVec_bvec] at this
    rw [this, Matrix.one_apply, bvec, Pi.single_apply]
  by_cases hi : r ≤ i.val
  · rw [h3 i j (by omega) (by omega) hi, Matrix.one_apply]
  · have hi' : i.val < r := by omega
    have h := (hfix ⟨i.val, hi'⟩ (by simpa using hi')).2
    have h1 := herm_UH hU (bvec j) (bvec (esI k r ⟨i.val, hi'⟩))
    rw [h, herm_bvec_right, herm_bvec_right, Hpk_mulVec, Hpk_mulVec] at h1
    have es : GBasic.sig k r (esI k r ⟨i.val, hi'⟩) = i := by
      apply Fin.ext
      have hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val := rfl
      rw [GBasic.sig_hi k r _ (by rw [hv]; omega), hv]
      omega
    have sg : GBasic.sgn k r (esI k r ⟨i.val, hi'⟩) = 1 := by
      have hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val := rfl
      unfold GBasic.sgn
      rw [if_neg (by rw [hv]; omega)]
    rw [es, sg, one_mul, one_mul, mulVec_bvec] at h1
    rw [h1, Matrix.one_apply, bvec, Pi.single_apply]
theorem psi_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have : ell k r z 1 = 0 := by
    unfold ell
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with h
    · rw [Matrix.one_apply, if_neg]
      intro e
      have := congrArg Fin.val e
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact hz _ (Or.inl a.isLt)
  unfold psi
  rw [this]
  simp
def Dp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Mx k r) := {g | 0 < GGl k r z z' g}
theorem Dp_open (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Dp k r z z') :=
  isOpen_lt continuous_const (GGl_continuous k r z z')
theorem Slev_last {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {s : Mx k r} (hs : s ∈ Slev k r z (Fin.last r)) :
    s ∈ UWset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Nlev_last hm, mul_one]
  exact hh
theorem Dp_dom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsDom k r z z' (Fin.last r) (Dp k r z z') := by
  refine ⟨Dp_open k r z z', ?_⟩
  rintro g ⟨-, hg⟩ s hs s' hs'
  show 0 < GGl k r z z' (s * g * s')
  rw [GG_inv (Slev_last hs) (Slev_last hs')]
  exact hg
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
theorem slice_smooth {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    SmoothLev k r (Fin.last r) (Dp k r z z') (Φ c) := by
  rintro g₀ ⟨hg, hD⟩
  obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2.1 (c, g₀) ⟨hc, hg, hD⟩
  refine ⟨(fun g => (c, g)) ⁻¹' U, fun g => F (c, g), hU.preimage (by fun_prop), hx, ?_,
    fun g hg hgl => hΦF (c, g) hg hgl⟩
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg)
theorem slice_FF (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π')
    {c : Fin r → ℂ} (hc : c ∈ OmX r) : Φ c ∈ FFl k r z z' π π' (Fin.last r) (Dp k r z z') := by
  refine ⟨slice_smooth hΦ hc, ?_, ?_, ?_⟩
  · intro g _ n hn
    rw [Nlev_last hn, one_mul, psi_one hz, one_smul]
  · intro g _ n hn
    rw [Nlev_last hn, mul_one, psi_one hz', one_smul]
  · rintro g ⟨hg, hD⟩ h hh h' hh'
    exact hΦ.2.2 (c, g) ⟨hc, hg, hD⟩ h hh h' hh'
end Geo
section Exist
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
def tFun (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) (Φ : Fn k r (Wq →L[ℂ] Wp)) :
    Fn k r (Wq →L[ℂ] Wp) :=
  fun c g => (DomR k r z z').indicator (fun x => tL k r z z' (Fin.last r) Y a b (Φ x.1) x.2) (c, g)
theorem tFun_mem (hTP : TPreservesFF) (hJS : TJointSmooth) (hz : inWb k r z) (hz' : inWb k r z') (Y : ℂ) (a b : Fin 2)
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') : tFun k r z z' Y a b Φ ∈ RadSp k r z z' π π' := by
  refine ⟨fun x hx => Set.indicator_of_notMem hx _, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · have hS : SmoothFam k r (Fin.last r) (OpR k r z z') Φ := fun x hx hg => hΦ.2.1 x (mem_DomR_of_OpR hx hg)
    obtain ⟨U, F, hU, hxU, hF, hE⟩ := hJS _ k r z z' (Fin.last r) (OpR k r z z') Φ Y a b (isOpen_OpR k r z z') hS
      x₀ (DomR_sub_OpR hx₀) hx₀.2.1
    refine ⟨U ∩ OpR k r z z', F, hU.inter (isOpen_OpR k r z z'), ⟨hxU, DomR_sub_OpR hx₀⟩,
      hF.mono Set.inter_subset_left, fun x hx hg => ?_⟩
    rw [← hE x hx.1 hg]
    exact Set.indicator_of_mem (mem_DomR_of_OpR hx.2 hg) _
  · have h1 := hTP Wp Wq k r z z' π π' (Fin.last r) (Dp k r z z') Y a b hz hz' (Dp_dom k r z z') _
      (slice_FF hz hz' hΦ hx.1)
    have h2 := h1.2.2.2 x.2 ⟨hx.2.1, hx.2.2⟩ h hh h' hh'
    unfold tFun
    rw [Set.indicator_of_mem (DomR_inv hh hh' hx), Set.indicator_of_mem (show (x.1, x.2) ∈ DomR k r z z' from hx)]
    exact h2
theorem tFun_lin (hLL : TLinLoc) (Y : ℂ) (a b : Fin 2) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k r z z' π π') (hΨ : Ψ ∈ RadSp k r z z' π π') (s : ℂ) :
    tFun k r z z' Y a b (Φ + s • Ψ) = tFun k r z z' Y a b Φ + s • tFun k r z z' Y a b Ψ := by
  funext c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · simp only [tFun, Pi.add_apply, Pi.smul_apply]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    exact (hLL _ k r z z' (Fin.last r) (Dp k r z z') Y a b (Φ c) (Ψ c) s (Dp_open k r z z') (slice_smooth hΦ hx.1)
      (slice_smooth hΨ hx.1) g ⟨hx.2.1, hx.2.2⟩).1
  · simp only [tFun, Pi.add_apply, Pi.smul_apply]
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp
def mkEnd {V : Type*} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (T : V → V) (hm : ∀ x ∈ S, T x ∈ S)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ∀ s : ℂ, T (x + s • y) = T x + s • T y) : Module.End ℂ S where
  toFun x := ⟨T x, hm x x.2⟩
  map_add' x y := by
    apply Subtype.ext
    have := hl x x.2 y y.2 1
    simpa using this
  map_smul' s x := by
    apply Subtype.ext
    have h0 : T 0 = 0 := by
      have := hl 0 S.zero_mem 0 S.zero_mem 1
      simpa using this
    have := hl 0 S.zero_mem x x.2 s
    simpa [h0] using this
theorem mkEnd_apply {V : Type*} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (T : V → V) (hm : ∀ x ∈ S, T x ∈ S)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ∀ s : ℂ, T (x + s • y) = T x + s • T y) (x : S) : (mkEnd S T hm hl x : V) = T x := rfl
def actualOps (hTP : TPreservesFF) (hLL : TLinLoc) (hJS : TJointSmooth) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 ≤ Tz k r z * Tz k r z') : ActualOps k r z z' π π' where
  t Y a b := mkEnd (RadSp k r z z' π π') (tFun k r z z' Y a b) (fun _ h => tFun_mem hTP hJS hz hz' Y a b h)
    (fun _ hx _ hy s => tFun_lin hLL Y a b hx hy s)
  op l j := mkEnd (RadSp k r z z' π π') (crd (opL l j)) (fun _ h => crd_mem l j h)
    (fun _ hx _ hy s => crd_lin l j hx hy s)
  fn j := mkEnd (RadSp k r z z' π π') (fun Φ c g => fnVal k r z z' j g • Φ c g) (fun _ h => fn_mem hT j h)
    (fun x _ y _ s => by
      funext c g
      simp only [Pi.add_apply, Pi.smul_apply]
      module)
  t_apply Y a b Φ x hx := by
    rw [mkEnd_apply]
    exact Set.indicator_of_mem (show (x.1, x.2) ∈ DomR k r z z' from hx) _
  op_apply l j Φ := rfl
  fn_apply j Φ x hx := rfl
end Exist
section Nat
open Qx2
variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {i : Fin (r + 1)} {D : Set (Mx k r)}
def Ntw (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (φ : E →L[ℂ] E') (T : (Mx k r → E) → Mx k r → E)
    (T' : (Mx k r → E') → Mx k r → E') : Prop :=
  ∀ f, SmoothLev k r i D f → ∀ x ∈ Glev k r i ∩ D, T' (fun y => φ (f y)) x = φ (T f x)
theorem Ntw.comp {φ : E →L[ℂ] E'} {T S : (Mx k r → E) → Mx k r → E} {T' S' : (Mx k r → E') → Mx k r → E'}
    (hT : Ntw k r i D φ T T') (hS : Ntw k r i D φ S S') (hSg : Good k r i D S) (hT'g : Good k r i D T') :
    Ntw k r i D φ (fun f => T (S f)) (fun f => T' (S' f)) := by
  intro f hf x hx
  show T' (S' fun y => φ (f y)) x = φ (T (S f) x)
  rw [hT'g.loc _ (fun y => φ (S f y)) (hS f hf) x hx]
  exact hT _ (hSg.sm _ hf) x hx
end Nat
section Adj
open Qx2
variable {k r : ℕ}
variable {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
def coefL (e : Wp) (v : Wq) : (Wq →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp v)
end Adj
section Alg
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
structure CovRel (E : Fin n → Fin n → A) (η : Fin n → A) (x : Fin n → ℂ) (ζ : A) : Prop where
  Eη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0
  Eζ : ∀ a b, E a b * ζ - ζ * E a b = x b • η a
variable {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}
end Alg
section Alg2
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}
end Alg2
section Dual
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
def Eop (E : Fin n → Fin n → A) : Fin n → Fin n → A := fun a b => -E b a
def dP (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (θ : Fin t → ℂ) (σ τ : Equiv.Perm (Fin t)) : A :=
  (List.ofFn fun k : Fin t => Tm E (θ k) (a (σ k)) (b (τ k))).prod
def dsum (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (θ : Fin t → ℂ) : A :=
  ∑ τ : Equiv.Perm (Fin t), ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * dP E a b θ σ τ)
end Dual
section Alg4
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {y : Fin n → A} {ξ : Fin n → ℂ} {ζb : A}
structure VecRel (E : Fin n → Fin n → A) (y : Fin n → A) (ξ : Fin n → ℂ) (ζb : A) : Prop where
  Ey : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0
  Eζ : ∀ a b, E a b * ζb - ζb * E a b = -(ξ a • y b)
end Alg4
section GlLev
open Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def LieC (k r : ℕ) (i : Fin (r + 1)) (Z : Mx k r) : Prop :=
  inLieLev k r i (hpart1 (Hpk k r) Z) ∧ inLieLev k r i (hpart2 (Hpk k r) Z)
end GlLev
section Leib
open Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
theorem smooth_mul {c : Mx k r → ℂ} {f : Mx k r → E} (hc : SmoothLev k r i D c) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun y => c y • f y) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  obtain ⟨U₂, C, hU₂, hgU₂, hC, he₂⟩ := hc g₀ hg₀
  refine ⟨U ∩ U₂, fun x => C x • F x, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hC.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hxG => ?_⟩
  show c x • f x = C x • F x
  rw [he x hx.1 hxG, he₂ x hx.2 hxG]
theorem smooth_linear (L : Mx k r →ₗ[ℂ] ℂ) : SmoothLev k r i D (fun y => L y) := fun _ _ =>
  ⟨Set.univ, fun y => L y, isOpen_univ, trivial,
    (((LinearMap.toContinuousLinearMap L).contDiff (n := ∞)).restrict_scalars ℝ).contDiffOn, fun _ _ _ => rfl⟩
def actL (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (u : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℂ] ℂ where
  toFun M := Λ (M *ᵥ u)
  map_add' a b := by rw [Matrix.add_mulVec, map_add]
  map_smul' a b := by rw [Matrix.smul_mulVec, map_smul]; rfl
theorem uh_inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq']
theorem smooth_inv (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    SmoothLev k r i D (fun y => Λ (y⁻¹ *ᵥ v)) := by
  let L : Mx k r →ₗ[ℝ] ℂ :=
    { toFun := fun g => Λ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v)
      map_add' := fun x y => by
        simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun c x => by
        simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec] }
  intro g₀ _
  refine ⟨Set.univ, fun y => L y, isOpen_univ, trivial, (LinearMap.toContinuousLinearMap L).contDiff.contDiffOn,
    fun y _ hy => ?_⟩
  show Λ (y⁻¹ *ᵥ v) = Λ ((Hpk k r * yᴴ * Hpk k r) *ᵥ v)
  rw [uh_inv_eq hy.1]
end Leib
section OpRing
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def VS (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ (Mx k r → E) where
  carrier := {f | SmoothLev k r i D f ∧ ∀ x, x ∉ Glev k r i ∩ D → f x = 0}
  zero_mem' := ⟨smooth_zero, fun _ _ => rfl⟩
  add_mem' := fun {f g} hf hg => ⟨smooth_add hf.1 hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  smul_mem' := fun c f hf => ⟨smooth_smul hf.1 c, fun x hx => by simp [hf.2 x hx]⟩
def cut (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (f : Mx k r → E) : Mx k r → E := (Glev k r i ∩ D).indicator f
theorem cut_of_mem (f : Mx k r → E) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : cut k r i D f g = f g :=
  Set.indicator_of_mem hg f
theorem cut_mem (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) : cut k r i D f ∈ VS k r i D E := by
  refine ⟨fun g₀ hg₀ => ?_, fun x hx => Set.indicator_of_notMem hx f⟩
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  exact ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left,
    fun g hg hgl => by rw [cut_of_mem f ⟨hgl, hg.2⟩, he g hg.1 hgl]⟩
def hat (hD : IsOpen D) (T : (Mx k r → E) → Mx k r → E) (hT : Good k r i D T) : Module.End ℂ (VS k r i D E) :=
  mkEnd (VS k r i D E) (fun f => cut k r i D (T f)) (fun f hf => cut_mem hD (hT.sm f hf.1))
    (fun x hx y hy s => by
      funext g
      by_cases hg : g ∈ Glev k r i ∩ D
      · show cut k r i D (T (x + s • y)) g = cut k r i D (T x) g + s • cut k r i D (T y) g
        rw [cut_of_mem _ hg, cut_of_mem _ hg, cut_of_mem _ hg]
        exact hT.lin x y s hx.1 hy.1 g hg
      · show cut k r i D (T (x + s • y)) g = cut k r i D (T x) g + s • cut k r i D (T y) g
        simp [cut, Set.indicator_of_notMem hg])
def Rep (X : Module.End ℂ (VS k r i D E)) (T : (Mx k r → E) → Mx k r → E) : Prop :=
  ∀ v : VS k r i D E, ∀ g ∈ Glev k r i ∩ D, (X v : Mx k r → E) g = T (v : Mx k r → E) g
def Eh (hD : IsOpen D) (a b : Fin (mdim k r i)) : Module.End ℂ (VS k r i D E) := hat hD _ (good_eh hD a b)
theorem good_mul {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) :
    Good k r i D (fun (f : Mx k r → E) y => c y • f y) :=
  ⟨fun _ hf => smooth_mul hc hf, fun f f₂ h x hx => by simp only [h x hx],
    fun f f₂ s _ _ x _ => by simp only [smul_add, smul_comm (c x) s]⟩
def Mh (hD : IsOpen D) (c : Mx k r → ℂ) (hc : SmoothLev k r i D c) : Module.End ℂ (VS k r i D E) :=
  hat hD _ (good_mul hc)
end OpRing
section Concrete
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def hermL (k r : ℕ) (x₀ : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun v := herm (Hpk k r) v x₀
  map_add' a b := by simp [herm, Matrix.mulVec_add, dotProduct_add]
  map_smul' a b := by simp [herm, Matrix.mulVec_smul, dotProduct_smul]
variable (z z' : Fin (2 * r + k + 1) → ℂ)
theorem sm_eta (c : Fin (mdim k r i)) : SmoothLev k r i D (fun g => ybv k r z i g c) :=
  smooth_linear (actL (hermL k r (fvec k r z i)) (bvec (posL k r i c)))
theorem sm_zeta : SmoothLev k r i D (zetaL k r z z' i) :=
  smooth_linear (actL (hermL k r (fvec k r z i)) (fvec k r z' i))
theorem sm_y (c : Fin (mdim k r i)) : SmoothLev k r i D (fun g => yv k r z i g c) :=
  smooth_inv (LinearMap.proj (posL k r i c)) (fvec k r z i)
def zbF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (g : Mx k r) : ℂ :=
  herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i)
theorem sm_zb : SmoothLev k r i D (zbF k r z z' i) := smooth_inv (hermL k r (fvec k r z' i)) (fvec k r z i)
abbrev Mop (k r : ℕ) (i : Fin (r + 1)) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) (f : Mx k r → E) : Mx k r → E :=
  qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w f
end Concrete
section Comb
variable {X : Type*} [AddCommGroup X] [Module ℂ X]
end Comb
section Final
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def ComRule (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : Mx k r → ℂ) (g : Mx k r) (ρ κ : Fin (mdim k r i) → ℂ) (s d : ℂ) : Prop :=
  ∀ (t : ℕ) (a b : Fin t → Fin (mdim k r i)) (w : ℂ) (f : Mx k r → E), SmoothLev k r i D f →
    Mop k r i a b w (fun y => c y • f y) g = c g • Mop k r i a b w f g +
      s • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) f g
def ch (k r : ℕ) (i : Fin (r + 1)) (A B : Fin (mdim k r i) → ℂ) (w : ℂ) (f : Mx k r → E) (g : Mx k r) : E :=
  ∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * A p * B q) •
    Mop k r i (skip1 p) (skip1 q) w f g
def ch2 (k r : ℕ) (i : Fin (r + 1)) (A A' B B' : Fin (mdim k r i) → ℂ) (w : ℂ) (f : Mx k r → E) (g : Mx k r) : E :=
  ∑ p : Fin (mdim k r i), ∑ p' : Fin (mdim k r i), ∑ q : Fin (mdim k r i), ∑ q' : Fin (mdim k r i),
    if p < p' ∧ q < q' then
      ((-1 : ℂ) ^ ((p : ℕ) + (p' : ℕ) + (q : ℕ) + (q' : ℕ)) * (A p * A' p' - A p' * A' p) * (B q * B' q' - B q' * B' q)) •
        Mop k r i (skip2 p p') (skip2 q q') w f g
    else 0
variable {c : Mx k r → ℂ} {g : Mx k r} {ρ κ : Fin (mdim k r i) → ℂ} {s d : ℂ}
end Final
end Formalism.FourierDecayAlt.P.Qx5
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


