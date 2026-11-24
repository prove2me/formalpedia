-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:46.56472+00:00
-- url     : https://prove2.me/theorems/519a8920-6ff4-4763-9733-649fcc808dad
-- title:
--   Compactly Supported Banach Model
-- statement:
--   Definitions and structural lemmas for Compactly Supported Banach Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cc_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_mulL_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dLR_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_coefficient_linear
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section abstract
variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]
end abstract
section smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
end smooth
def prj (Z : Mat k r) : Mat k r := (1 / 2 : ℂ) • (Z - Hpk k r * Zᴴ * Hpk k r)
def kap (Y : Mat k r) : Mat k r := (1 + Y) * (1 - Y)⁻¹
def iot (Z : Mat k r) : Mat k r := (Z - 1) * (Z + 1)⁻¹
section smooth2
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
end smooth2
abbrev J (k r : ℕ) : Type := Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool
def Eb (i : J k r) : Mat k r :=
  Matrix.of fun p q => if p = i.1 ∧ q = i.2.1 then (if i.2.2 then Complex.I else 1) else 0
def Mv (Y : J k r → ℝ) : Mat k r :=
  Matrix.of fun p q => ((Y (p, q, false) : ℝ) : ℂ) + ((Y (p, q, true) : ℝ) : ℂ) * Complex.I
def co (Z : Mat k r) : J k r → ℝ := fun i => if i.2.2 then (Z i.1 i.2.1).im else (Z i.1 i.2.1).re
def Lt (i : J k r) : Mat k r := (nrm (true, prj (Eb i))).2
def kc (i : J k r) (Z : Mat k r) : ℝ := co Z i * ‖prj (Eb i)‖
def chart (g0 : Mat k r) (Y : J k r → ℝ) : Mat k r := kap (prj (Mv Y)) * g0
def Dom (k r : ℕ) : Set (J k r → ℝ) := {Y | IsUnit (1 - prj (Mv Y)).det}
def mulB (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => mulL A
      map_add' := fun A B => by ext g : 1; simp [mulL_apply, Matrix.add_mul]
      map_smul' := fun c A => by ext g : 1; simp [mulL_apply] }
def cT (k r : ℕ) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun c A => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
          conjTranspose_smul]
        simp only [RCLike.star_def, RCLike.conj_ofReal] }
def ebv (b : J k r) : J k r → ℝ := fun j => if b = j then 1 else 0
def sC (g0 : Mat k r) (i b : J k r) (Y : J k r → ℝ) : ℝ :=
  kc i (-(fderiv ℝ (chart g0) Y (ebv b)) * (chart g0 Y)⁻¹)
def aC (g0 : Mat k r) (i : J k r) (Y : J k r → ℝ) : (J k r → ℝ) →L[ℝ] ℝ :=
  ∑ b, sC g0 i b Y • ContinuousLinearMap.proj b
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  have hu : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hne : g ≠ 0 := by
    rintro rfl
    have : Nonempty (Fin (2 * r + k + 1)) := ⟨⟨0, by omega⟩⟩
    rw [Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra h; push Not at h; exact hne (Matrix.ext h)
  unfold gN
  apply Real.sqrt_pos.2
  calc (0:ℝ) < Complex.normSq (g i j) := Complex.normSq_pos.2 hij
    _ ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
def rho (g0 : Mat k r) (x : Mat k r) : J k r → ℝ := co (iot (x * g0⁻¹))
def Sr (g0 : Mat k r) : Set (Mat k r) := {x | IsUnit (x * g0⁻¹ + 1).det}
def Vd (mm : ℕ) (u w : List (Mat k r)) (g : Mat k r) : Prop :=
  (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ w, unitLie k r X) ∧ u.length + w.length ≤ mm ∧ g ∈ GV k r
abbrev Idx (k r mm : ℕ) : Type := {p : (List (Mat k r) × List (Mat k r)) × Mat k r // Vd mm p.1.1 p.1.2 p.2}
abbrev Lp (k r mm : ℕ) (E : Type*) [NormedAddCommGroup E] : Type _ := lp (fun _ : Idx k r mm => E) ⊤
def Tf (a : ℝ) (mm : ℕ) (F : Mat k r → E) : Idx k r mm → E :=
  fun i => ((gN i.1.2 ^ a : ℝ) : ℂ) • dLR i.1.1.1 i.1.1.2 F i.1.2
open Classical in

def Kf (a : ℝ) {mm : ℕ} (x : Idx k r mm → E) (u w : List (Mat k r)) (g : Mat k r) : E :=
  if h : Vd mm u w g then ((gN g ^ (-a) : ℝ) : ℂ) • x ⟨((u, w), g), h⟩ else 0
lemma Kf_add (a : ℝ) {mm : ℕ} (f f' : Idx k r mm → E) (u w : List (Mat k r)) (g : Mat k r) :
    Kf a (f + f') u w g = Kf a f u w g + Kf a f' u w g := by
  unfold Kf; split_ifs
  · rw [Pi.add_apply, smul_add]
  · simp
lemma Kf_smul (a : ℝ) {mm : ℕ} (s : ℂ) (f : Idx k r mm → E) (u w : List (Mat k r)) (g : Mat k r) :
    Kf a (s • f) u w g = s • Kf a f u w g := by
  unfold Kf; split_ifs
  · rw [Pi.smul_apply, smul_comm]
  · simp
lemma norm_rsmul (x : ℝ) (hx : 0 ≤ x) (e : E) : ‖((x : ℝ) : ℂ) • e‖ = x * ‖e‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
lemma rsmul_cancel {g : Mat k r} (hg : g ∈ GV k r) (a : ℝ) (e : E) :
    ((gN g ^ (-a) : ℝ) : ℂ) • ((gN g ^ a : ℝ) : ℂ) • e = e := by
  rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (gN_pos hg), neg_add_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_smul]
lemma Tf_inv {a : ℝ} {mm : ℕ} {x : Idx k r mm → E} {F : Mat k r → E} (hx : x = Tf a mm F)
    {u w : List (Mat k r)} {g : Mat k r} (h : Vd mm u w g) :
    dLR u w F g = ((gN g ^ (-a) : ℝ) : ℂ) • x ⟨((u, w), g), h⟩ := by
  rw [hx]; exact (rsmul_cancel h.2.2.2 a _).symm
lemma Kf_eq {a : ℝ} {mm : ℕ} {x : Idx k r mm → E} {F : Mat k r → E} (hx : x = Tf a mm F)
    {g : Mat k r} (hg : g ∈ GV k r) : Kf a x [] [] g = F g := by
  have h : Vd mm [] [] g := ⟨by simp, by simp, by simp, hg⟩
  rw [Kf, dif_pos h, ← Tf_inv hx h]; rfl
lemma dLR_zero (u v : List (Mat k r)) : dLR u v (0 : Mat k r → E) = 0 := by
  rw [dLR_eq]
  have := W_smul (lr u v) (0 : ℂ) (0 : Mat k r → E)
  simpa using this
lemma cc_zero (A : ℝ) (m : ℕ) : CCle A m (0 : Mat k r → E) 0 :=
  ⟨fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun u v _ _ _ g _ => by simp [dLR_zero]⟩
lemma ckOn_congr {F F' : Mat k r → E} {m : ℕ∞} (h : ∀ g ∈ GV k r, F g = F' g)
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) F' := by
  intro g0 hg0
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF g0 hg0
  exact ⟨U, f', hU, hgU, hc, fun g hg hgG => (h g hgG).symm.trans (hff g hg hgG)⟩
lemma cc_congr {F F' : Mat k r → E} {A c : ℝ} {m : ℕ} (h : ∀ g ∈ GV k r, F g = F' g)
    (hF : CCle A m F c) : CCle A m F' c := by
  refine ⟨ckOn_congr h hF.1, fun u v hu hv hl g hg => ?_⟩
  have e : dLR u v F g = dLR u v F' g := by
    rw [dLR_eq, dLR_eq]; exact W_congr _ (allLie_lr hu hv) h g hg
  rw [← e]; exact hF.2 u v hu hv hl g hg
lemma dLR_add' {F F' : Mat k r → E} {A c c' : ℝ} {m : ℕ} (hF : CCle A m F c) (hF' : CCle A m F' c')
    {u v : List (Mat k r)} {g : Mat k r} (h : Vd m u v g) :
    dLR u v (F + F') g = dLR u v F g + dLR u v F' g := by
  have hl' : (lr u v).length ≤ m := by rw [length_lr]; exact h.2.2.1
  rw [dLR_eq, dLR_eq, dLR_eq]
  exact W_add _ (allLie_lr h.1 h.2.1) (ckOn_mono hl' hF.1) (ckOn_mono hl' hF'.1) g h.2.2.2
def Vs (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) : Submodule ℂ (Lp k r mm E) where
  carrier := {x | ∃ F : Mat k r → E, InCC a mm F ∧ (∀ g ∈ GV k r, g ∉ S → F g = 0) ∧ ⇑x = Tf a mm F}
  zero_mem' := ⟨0, ⟨0, cc_zero a mm⟩, fun _ _ _ => rfl, by funext i; simp [Tf, dLR_zero]⟩
  add_mem' := by
    rintro x y ⟨F, ⟨c, hF⟩, hFS, hx⟩ ⟨F', ⟨c', hF'⟩, hF'S, hy⟩
    refine ⟨F + F', ⟨c + c', (matrix_coefficient_linear k r E a mm F F' c c' 1 hF hF').1⟩,
      fun g hg hgS => by simp [hFS g hg hgS, hF'S g hg hgS], ?_⟩
    rw [lp.coeFn_add, hx, hy]
    funext i
    simp only [Pi.add_apply, Tf]
    rw [dLR_add' hF hF' i.2, smul_add]
  smul_mem' := by
    rintro s x ⟨F, ⟨c, hF⟩, hFS, hx⟩
    refine ⟨s • F, ⟨‖s‖ * c, (matrix_coefficient_linear k r E a mm F F c c s hF hF).2⟩,
      fun g hg hgS => by simp [hFS g hg hgS], ?_⟩
    rw [lp.coeFn_smul, hx]
    funext i
    simp only [Pi.smul_apply, Tf]
    have e : dLR i.1.1.1 i.1.1.2 (s • F) i.1.2 = s • dLR i.1.1.1 i.1.1.2 F i.1.2 := by
      rw [dLR_eq, dLR_eq, W_smul]; rfl
    rw [e, smul_comm]
def evL {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) :
    Vs E a mm S →ₗ[ℂ] (Mat k r → E) where
  toFun x := Kf a (⇑(x : Lp k r mm E)) [] []
  map_add' x y := by
    funext g
    show Kf a (⇑((x + y : Vs E a mm S) : Lp k r mm E)) [] [] g =
      Kf a (⇑(x : Lp k r mm E)) [] [] g + Kf a (⇑(y : Lp k r mm E)) [] [] g
    rw [Submodule.coe_add, lp.coeFn_add, Kf_add]
  map_smul' s x := by
    funext g
    show Kf a (⇑((s • x : Vs E a mm S) : Lp k r mm E)) [] [] g = s • Kf a (⇑(x : Lp k r mm E)) [] [] g
    rw [Submodule.coe_smul, lp.coeFn_smul, Kf_smul]
lemma mem_vs {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {a : ℝ} {mm : ℕ} {S : Set (Mat k r)}
    (x : Vs E a mm S) : ∃ F : Mat k r → E, InCC a mm F ∧ (∀ g ∈ GV k r, g ∉ S → F g = 0) ∧
      ⇑(x : Lp k r mm E) = Tf a mm F := x.2
def model {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) :
    Formalism.FourierDecayAlt.U.CCModel k r E a mm S (Vs E a mm S) where
  ev := evL a mm S
  mem x := by
    obtain ⟨F, ⟨c, hF⟩, -, hx⟩ := mem_vs x
    refine cc_congr (fun g hg => (Kf_eq hx hg).symm) ⟨hF.1, fun u v hu hv hl g hg => ?_⟩
    have h : Vd mm u v g := ⟨hu, hv, hl, hg⟩
    have e : ‖(x : Lp k r mm E) ⟨((u, v), g), h⟩‖ = gN g ^ a * ‖dLR u v F g‖ := by
      rw [hx]; exact norm_rsmul _ (Real.rpow_nonneg (gN_pos hg).le _) _
    rw [← e]; exact lp.norm_apply_le_norm (by simp) _ _
  least x c hc := by
    obtain ⟨F, -, -, hx⟩ := mem_vs x
    have hF : CCle a mm F c := cc_congr (fun g hg => Kf_eq hx hg) hc
    show ‖(x : Lp k r mm E)‖ ≤ c
    refine lp.norm_le_of_forall_le (cc_nonneg hF) fun i => ?_
    rw [hx]
    show ‖((gN i.1.2 ^ a : ℝ) : ℂ) • dLR i.1.1.1 i.1.1.2 F i.1.2‖ ≤ c
    rw [norm_rsmul _ (Real.rpow_nonneg (gN_pos i.2.2.2.2).le _)]
    exact hF.2 _ _ i.2.1 i.2.2.1 i.2.2.2.1 _ i.2.2.2.2
  off x g hg hgS := by
    obtain ⟨F, -, hFS, hx⟩ := mem_vs x
    show Kf a (⇑(x : Lp k r mm E)) [] [] g = 0
    rw [Kf_eq hx hg]; exact hFS g hg hgS
  surj F hF hFS := by
    obtain ⟨c, hc⟩ := hF
    have hm : Memℓp (Tf a mm F) ⊤ := by
      rw [memℓp_infty_iff]
      refine ⟨c, ?_⟩
      rintro _ ⟨i, rfl⟩
      show ‖((gN i.1.2 ^ a : ℝ) : ℂ) • dLR i.1.1.1 i.1.1.2 F i.1.2‖ ≤ c
      rw [norm_rsmul _ (Real.rpow_nonneg (gN_pos i.2.2.2.2).le _)]
      exact hc.2 _ _ i.2.1 i.2.2.1 i.2.2.2.1 _ i.2.2.2.2
    exact ⟨⟨⟨Tf a mm F, hm⟩, F, ⟨c, hc⟩, hFS, rfl⟩, fun g hg => Kf_eq rfl hg⟩
end Formalism.FourierDecayAlt.P.Ux1
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


