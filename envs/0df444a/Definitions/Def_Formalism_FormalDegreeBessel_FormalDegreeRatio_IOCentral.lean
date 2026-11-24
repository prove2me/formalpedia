-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:16:18.040606+00:00
-- url     : https://prove2.me/theorems/9ae4c8c4-1415-4d0b-9d07-9397951f0c58
-- title:
--   IOCentral
-- statement:
--   Definitions and structural lemmas for IOCentral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOCentral.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Theorems.Thm_Formalism_REAL_rdLinV
import Theorems.Thm_Formalism_REAL_rdSmoothV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
abbrev IOPt {n : ℕ} (ε : Fin n → Bool) : Type := {g : Matrix (Fin n) (Fin n) ℂ // inUJ ε g}
open Classical in

def ioExt {n : ℕ} (ε : Fin n → Bool) {E : Type} [Zero E] (φ : IOPt ε → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => if h : inUJ ε g then φ ⟨g, h⟩ else 0
section Core
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma io_inUJ_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inUJ ε A) (hB : inUJ ε B) :
    inUJ ε (A * B) := by
  unfold inUJ at hA hB ⊢
  calc (A * B)ᴴ * Jm ε * (A * B) = Bᴴ * (Aᴴ * Jm ε * A) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hA, hB]
lemma ioExt_at {φ : IOPt ε → E} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ioExt ε φ g = φ ⟨g, hg⟩ := by
  unfold ioExt
  rw [dif_pos hg]
lemma io_smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (hf : SmoothOnGV ε f) : SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => (h g hgJ).symm.trans (hfF g hg hgJ)⟩
lemma io_smooth_zero : SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
lemma io_smooth_add {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') : SmoothOnGV ε (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgJ => ?_⟩
  simp only [hfF g hg.1 hgJ, hfF' g hg.2 hgJ]
lemma io_smooth_smul {f : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ) (hf : SmoothOnGV ε f) :
    SmoothOnGV ε (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgJ => ?_⟩
  simp only [hfF g hg hgJ]
lemma Jm_mul_self_eq_oneFormalDegreeRatio {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num
lemma Jm_conjTranspose_eq_selfFormalDegreeRatio {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp
lemma inUJ_exp_of_inG_formal_degree_ratio {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  unfold inG at hY
  unfold inUJ
  have hYH : Yᴴ = Jm ε * -Y * (Jm ε)⁻¹ := by
    have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneFormalDegreeRatio ε)
    have h1 : Yᴴ * Jm ε * Jm ε = -(Jm ε * Y) * Jm ε := by rw [eq_neg_of_add_eq_zero_left hY]
    rw [Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one] at h1
    rw [h1, hJi, Matrix.mul_neg, Matrix.neg_mul]
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_oneFormalDegreeRatio ε, Jm_mul_self_eq_oneFormalDegreeRatio ε⟩, rfl⟩
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneFormalDegreeRatio ε)
  rw [← Matrix.exp_conjTranspose, hYH, Matrix.exp_conj _ _ hJu, hJi,
    Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]
lemma inG_real_smul_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (t : ℝ) : inG ε ((t : ℂ) • X) := by
  unfold inG at hX ⊢
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
lemma io_rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact h _ (io_inUJ_mul hg (inUJ_exp_of_inG_formal_degree_ratio (inG_real_smul_of_inG hX t)))
lemma inG_cpart1_formal_degree_ratio {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart1 ε Z) := by
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp only [star_div₀, star_one, star_ofNat]
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.one_mul]
  unfold inG cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_selfFormalDegreeRatio, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one, hJJ, smul_sub]
  abel
lemma inG_cpart2_formal_degree_ratio {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart2 ε Z) := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [star_div₀, star_one, star_mul', hI, star_ofNat]
    ring
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.one_mul]
  unfold inG cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose_eq_selfFormalDegreeRatio, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio, Matrix.mul_one, hJJ, smul_add, neg_smul]
  simp only [neg_smul, one_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc, Jm_mul_self_eq_oneFormalDegreeRatio,
    Matrix.mul_one]
  abel
lemma io_eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b f g = EabV ε a b f' g := by
  simp only [EabV, EcV]
  rw [io_rd_congr h (inG_cpart1_formal_degree_ratio ε _) hg, io_rd_congr h (inG_cpart2_formal_degree_ratio ε _) hg]
lemma io_eab_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n) :
    SmoothOnGV ε (EabV ε a b f) := by
  have h1 := rdSmoothV n ε E f (cpart1 ε (Matrix.single a b 1)) hf (inG_cpart1_formal_degree_ratio ε _)
  have h2 := rdSmoothV n ε E f (cpart2 ε (Matrix.single a b 1)) hf (inG_cpart2_formal_degree_ratio ε _)
  exact io_smooth_add h1 (io_smooth_smul Complex.I h2)
lemma io_eab_lin {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun h => f h + c • f' h) g = EabV ε a b f g + c • EabV ε a b f' g := by
  have h1 := (rdLinV n ε E f f' (cpart1 ε (Matrix.single a b 1)) (cpart1 ε (Matrix.single a b 1)) 0 c g
    hf hf' (inG_cpart1_formal_degree_ratio ε _) (inG_cpart1_formal_degree_ratio ε _) hg).2.2
  have h2 := (rdLinV n ε E f f' (cpart2 ε (Matrix.single a b 1)) (cpart2 ε (Matrix.single a b 1)) 0 c g
    hf hf' (inG_cpart2_formal_degree_ratio ε _) (inG_cpart2_formal_degree_ratio ε _) hg).2.2
  simp only [EabV, EcV]
  rw [h1, h2, smul_add, smul_add, smul_comm Complex.I c]
  abel
lemma io_eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    EabV ε a b (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) g = 0 := by
  simp only [EabV, EcV, RdV, deriv_const, smul_zero, add_zero]
variable (ε E) in

def ioS : Submodule ℂ (IOPt ε → E) where
  carrier := {φ | SmoothOnGV ε (ioExt ε φ)}
  add_mem' {φ ψ} hφ hψ :=
    io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.add_apply]) (io_smooth_add hφ hψ)
  zero_mem' := io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.zero_apply]) io_smooth_zero
  smul_mem' c φ hφ :=
    io_smooth_congr (fun g hg => by simp only [ioExt_at hg, Pi.smul_apply]) (io_smooth_smul c hφ)
def IORep (F : Matrix (Fin n) (Fin n) ℂ → E) (φ : IOPt ε → E) : Prop :=
  ∀ g (hg : inUJ ε g), F g = φ ⟨g, hg⟩
variable (ε) in

def ioT (a b : Fin n) (φ : IOPt ε → E) : IOPt ε → E := fun g => EabV ε a b (ioExt ε φ) g.1
lemma ioT_mem {φ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (a b : Fin n) : ioT ε a b φ ∈ ioS ε E := by
  show SmoothOnGV ε (ioExt ε (ioT ε a b φ))
  exact io_smooth_congr (fun g hg => (ioExt_at (φ := ioT ε a b φ) hg).symm) (io_eab_smooth hφ a b)
lemma ioT_add {φ ψ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (hψ : ψ ∈ ioS ε E) (a b : Fin n) :
    ioT ε a b (φ + ψ) = ioT ε a b φ + ioT ε a b ψ := by
  funext g
  show EabV ε a b (ioExt ε (φ + ψ)) g.1 = EabV ε a b (ioExt ε φ) g.1 + EabV ε a b (ioExt ε ψ) g.1
  rw [io_eab_congr (f := ioExt ε (φ + ψ)) (f' := fun h => ioExt ε φ h + (1 : ℂ) • ioExt ε ψ h)
    (fun h hh => by simp only [ioExt_at hh, Pi.add_apply, one_smul]) a b g.2,
    io_eab_lin hφ hψ 1 a b g.2, one_smul]
lemma ioT_smul {φ : IOPt ε → E} (hφ : φ ∈ ioS ε E) (c : ℂ) (a b : Fin n) :
    ioT ε a b (c • φ) = c • ioT ε a b φ := by
  funext g
  show EabV ε a b (ioExt ε (c • φ)) g.1 = c • EabV ε a b (ioExt ε φ) g.1
  rw [io_eab_congr (f := ioExt ε (c • φ))
    (f' := fun h => (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) h + c • ioExt ε φ h)
    (fun h hh => by simp only [ioExt_at hh, Pi.smul_apply, zero_add]) a b g.2,
    io_eab_lin io_smooth_zero hφ c a b g.2, io_eab_zero, zero_add]
variable (ε E) in

def ioE (a b : Fin n) : Module.End ℂ (ioS ε E) where
  toFun x := ⟨ioT ε a b x.1, ioT_mem x.2 a b⟩
  map_add' x y := Subtype.ext (ioT_add x.2 y.2 a b)
  map_smul' c x := Subtype.ext (ioT_smul x.2 c a b)
end Core
end Formalism.QuantumDeterminants


