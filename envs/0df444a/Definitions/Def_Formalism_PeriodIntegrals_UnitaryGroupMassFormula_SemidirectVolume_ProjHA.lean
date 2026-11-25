-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:51.663828+00:00
-- url     : https://prove2.me/theorems/10229884-45df-594b-b65c-325d3f3b4804
-- title:
--   Proj HA
-- statement:
--   Definitions and structural lemmas for Proj HA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjHA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_comp
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_id
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_uni
import Theorems.Thm_PI_VolSemiDirect_W_stabilizer_fixes_frame_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
section R
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
def datR : PG.Dat (R ⊗[F] E) (Fin M) r where
  σA := sigR R σ
  JA := JR R J
  e a := ratV (F := F) R (P.e a)
  f a := ratV (F := F) R (P.f a)
  z := ratV (F := F) R P.z
  tz := inclR (F := F) R ((algebraMap F E (-T))⁻¹)
theorem sigR_inclR (x : E) : sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id F R) σ (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight (σ x)
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
theorem hR_ratV (x y : Fin M → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR (F := F) R (hE σ J x y) := by
  unfold hR hE Formalism.UG.hform JR ratV
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_mul, sigR_inclR, Matrix.map_apply]
  rfl
variable {R σ J P T}
theorem datR_hyp (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) :
    (datR R σ J P T).Hyp := by
  have hT : algebraMap F E (-T) ≠ 0 := by
    rw [map_neg]
    exact neg_ne_zero.mpr ((map_ne_zero _).mpr hP.2.2.2.2.2.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show sigR R σ (sigR R σ x) = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show Algebra.TensorProduct.map (AlgHom.id F R) σ
          (Algebra.TensorProduct.map (AlgHom.id F R) σ (a ⊗ₜ b)) = a ⊗ₜ b
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.id_apply, hσσ]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  · intro i j
    show sigR R σ (inclR R (J j i)) = inclR R (J i j)
    rw [sigR_inclR, hJ.1]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.e b)) = 0
    rw [hR_ratV, hP.1 a b, map_zero]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.f b)) = 0
    rw [hR_ratV, hP.2.1 a b, map_zero]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.f b)) = if a = b then 1 else 0
    rw [hR_ratV, hP.2.2.1 a b]
    split_ifs <;> simp
  · intro a
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0
    rw [hR_ratV, hP.2.2.2.1 a, map_zero]
  · intro a
    show hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R P.z) = 0
    rw [hR_ratV, hP.2.2.2.2.1 a, map_zero]
  · show inclR (F := F) R ((algebraMap F E (-T))⁻¹) * hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
    rw [hR_ratV, hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀ hT, map_one]
theorem stabilizer_fixes_normal_vector {g : HA R σ J} (hg : g ∈ S0 R σ J P) :
    lin R σ J g (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
  have h := congrFun (MulAction.mem_stabilizer_iff.mp hg) (Fin.last r)
  change (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec
      (fun i => inclR R (F0 P (Fin.last r) i)) = fun i => inclR R (F0 P (Fin.last r) i) at h
  simp only [F0, Fin.snoc_last] at h
  exact h
theorem stabilizer_fixes_frame_and_normal {g : HA R σ J} (hg : g ∈ S0 R σ J P) :
    (datR R σ J P T).FixEZ (lin R σ J g) := by
  exact ⟨fun a => stabilizer_fixes_frame_vector R σ J P hg a, stabilizer_fixes_normal_vector hg⟩
theorem hform_eq_dotProduct_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σA : A →+* A)
    (JA : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σA JA x y = dotProduct (fun i => σA (x i)) (Matrix.mulVec JA y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
theorem hform_mulVec_mulVec_eq_hform_cT_mul_mul {A : Type} [CommRing A] {n : Type} [Fintype n] (σA : A →+* A)
    (JA Mx : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y) =
      Formalism.UG.hform σA (Formalism.UG.cT σA Mx * JA * Mx) x y := by
  have h1 : (fun i => σA (Matrix.mulVec Mx x i)) =
      Matrix.mulVec (Mx.map σA) (fun i => σA (x i)) := by
    funext i
    exact RingHom.map_mulVec σA Mx x i
  calc Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y)
      = dotProduct (Matrix.mulVec (Mx.map σA) (fun i => σA (x i)))
          (Matrix.mulVec JA (Matrix.mulVec Mx y)) := by
        rw [hform_eq_dotProduct_mulVec, h1]
    _ = dotProduct (fun i => σA (x i))
          (Matrix.mulVec (Mx.map σA).transpose (Matrix.mulVec JA (Matrix.mulVec Mx y))) := by
        symm
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = dotProduct (fun i => σA (x i)) (Matrix.mulVec (Formalism.UG.cT σA Mx * JA * Mx) y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        rfl
    _ = Formalism.UG.hform σA (Formalism.UG.cT σA Mx * JA * Mx) x y := (hform_eq_dotProduct_mulVec _ _ _ _).symm
theorem hform_single_single_semidirect_volume {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σA : A →+* A) (N : Matrix n n A) (i j : n) :
    Formalism.UG.hform σA N (Pi.single i 1) (Pi.single j 1) = N i j := by
  unfold Formalism.UG.hform
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp
theorem uni_lin (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := by
  intro x y
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J :=
    g.2
  show Formalism.UG.hform (sigR R σ) (JR R J)
      (Matrix.mulVec ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) x)
      (Matrix.mulVec ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) y) =
    Formalism.UG.hform (sigR R σ) (JR R J) x y
  rw [hform_mulVec_mulVec_eq_hform_cT_mul_mul, hg]
theorem uj_of_uni {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σA : A →+* A)
    (JA : Matrix n n A) (Mx : Matrix n n A)
    (h : ∀ x y, Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y) = Formalism.UG.hform σA JA x y) :
    Formalism.UG.cT σA Mx * JA * Mx = JA := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec_mulVec_eq_hform_cT_mul_mul, hform_single_single_semidirect_volume, hform_single_single_semidirect_volume] at h1
  exact h1
def piMat (g : HA R σ J) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  LinearMap.toMatrix' ((datR R σ J P T).Pi (lin R σ J g))
theorem piMat_mulVec (g : HA R σ J) (v : Fin M → R ⊗[F] E) :
    Matrix.mulVec (piMat (P := P) (T := T) g) v = (datR R σ J P T).Pi (lin R σ J g) v := by
  exact LinearMap.toMatrix'_mulVec _ v
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
theorem Pi_lin_mul {g g' : HA R σ J} (hg : g ∈ S0 R σ J P) (hg' : g' ∈ S0 R σ J P) :
    (datR R σ J P T).Pi (lin R σ J (g * g')) =
      (datR R σ J P T).Pi (lin R σ J g) ∘ₗ (datR R σ J P T).Pi (lin R σ J g') := by
  have H := datR_hyp (R := R) (T := T) hσσ hJ hP
  have hl : lin R σ J (g * g') = lin R σ J g ∘ₗ lin R σ J g' := by
    unfold lin
    rw [← Matrix.mulVecLin_mul]
    rfl
  refine LinearMap.ext (fun v => ?_)
  rw [hl, LinearMap.comp_apply]
  exact (PG.Dat.Pi_comp H (fun a => stabilizer_fixes_frame_vector R σ J P hg a) (stabilizer_fixes_frame_and_normal hg') (uni_lin g') v).symm
theorem Pi_lin_one :
    (datR R σ J P T).Pi (lin R σ J 1) = LinearMap.id := by
  have H := datR_hyp (R := R) (T := T) hσσ hJ hP
  have hl : lin R σ J (1 : HA R σ J) = LinearMap.id := by
    unfold lin
    rw [show ((HA.mat R σ J 1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = 1
      from rfl, Matrix.mulVecLin_one]
  rw [hl]
  exact LinearMap.ext (fun v => PG.Dat.Pi_id H v)
def piU (g : HA R σ J) (hg : g ∈ S0 R σ J P) : GL (Fin M) (R ⊗[F] E) where
  val := piMat (P := P) (T := T) g
  inv := piMat (P := P) (T := T) g⁻¹
  val_inv := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP hg ((S0 R σ J P).inv_mem hg), mul_inv_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]
  inv_val := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP ((S0 R σ J P).inv_mem hg) hg, inv_mul_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]
theorem piU_mem (g : HA R σ J) (hg : g ∈ S0 R σ J P) : piU hσσ hJ hP g hg ∈ HR R σ J := by
  have H := datR_hyp (R := R) (T := T) hσσ hJ hP
  show Formalism.UG.cT (sigR R σ) (piMat (P := P) (T := T) g) * JR R J * piMat (P := P) (T := T) g = JR R J
  apply uj_of_uni
  intro x y
  rw [piMat_mulVec, piMat_mulVec]
  exact PG.Dat.Pi_uni H (stabilizer_fixes_frame_and_normal hg) (uni_lin g) x y
def piG (g : HA R σ J) (hg : g ∈ S0 R σ J P) : HA R σ J := ⟨piU hσσ hJ hP g hg, piU_mem hσσ hJ hP g hg⟩
end R
end PI.VolSemiDirect.W


