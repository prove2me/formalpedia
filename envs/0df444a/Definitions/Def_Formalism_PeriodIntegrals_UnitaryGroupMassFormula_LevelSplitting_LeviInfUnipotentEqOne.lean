-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:38.614237+00:00
-- url     : https://prove2.me/theorems/9a2de35e-3148-5381-bdbd-50aec422de17
-- title:
--   Levi Inf Unipotent Eq One
-- statement:
--   Definitions and structural lemmas for Levi Inf Unipotent Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LeviInfUnipotentEqOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_comp
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_one
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_uni
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
section R
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
def uT (g : HA R σ J) : Matrix (Fin r) (Fin r) (R ⊗[F] E) :=
  Matrix.of fun a b => if a < b then
    hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J g (ratV (F := F) R (P.e b)))
    else if a = b then 1 else 0
theorem det_uT (g : HA R σ J) : (uT R σ J P g).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun a _ => by simp [uT]
  · intro i j hji
    have h : j < i := hji
    simp only [uT, Matrix.of_apply]
    rw [if_neg (lt_asymm h), if_neg (ne_of_gt h)]
def uI (g : HA R σ J) : Matrix (Fin r) (Fin r) (R ⊗[F] E) := (uT R σ J P g).adjugate
theorem uT_mul_uI (g : HA R σ J) : uT R σ J P g * uI R σ J P g = 1 := by
  rw [uI, Matrix.mul_adjugate, det_uT, one_smul]
theorem uI_mul_uT (g : HA R σ J) : uI R σ J P g * uT R σ J P g = 1 := by
  rw [uI, Matrix.adjugate_mul, det_uT, one_smul]
def cj (U : Matrix (Fin r) (Fin r) (R ⊗[F] E)) : Matrix (Fin r) (Fin r) (R ⊗[F] E) :=
  Matrix.of fun a b => sigR R σ (U b a)
theorem cj_apply (U : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (a b : Fin r) :
    cj R σ U a b = sigR R σ (U b a) := rfl
theorem cj_mul (U V : Matrix (Fin r) (Fin r) (R ⊗[F] E)) : cj R σ U * cj R σ V = cj R σ (V * U) := by
  ext a b
  simp only [cj, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
theorem cj_one : cj R σ (1 : Matrix (Fin r) (Fin r) (R ⊗[F] E)) = 1 := by
  ext a b
  simp only [cj, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]
variable {R σ J P T}
section Hyp
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
theorem levTI (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))
      (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)) x) = x := by
  rw [levL_comp (datR_hyp hσσ hJ hP), uT_mul_uI, cj_mul, uT_mul_uI, cj_one,
    levL_one (datR_hyp hσσ hJ hP)]
theorem levIT (g : HA R σ J) (x : Fin M → R ⊗[F] E) :
    levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))
      (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)) x) = x := by
  rw [levL_comp (datR_hyp hσσ hJ hP), uI_mul_uT, cj_mul, uI_mul_uT, cj_one,
    levL_one (datR_hyp hσσ hJ hP)]
end Hyp
def levU (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (g : HA R σ J) :
    GL (Fin M) (R ⊗[F] E) where
  val := LinearMap.toMatrix' (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g)))
  inv := LinearMap.toMatrix' (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g)))
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have : (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))).comp
        (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))) = LinearMap.id :=
      LinearMap.ext fun x => levTI hσσ hJ hP g x
    rw [this, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have : (levL (datR R σ J P T) (uI R σ J P g) (cj R σ (uT R σ J P g))).comp
        (levL (datR R σ J P T) (uT R σ J P g) (cj R σ (uI R σ J P g))) = LinearMap.id :=
      LinearMap.ext fun x => levIT hσσ hJ hP g x
    rw [this, LinearMap.toMatrix'_id]
section Hyp2
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
theorem levU_mem (g : HA R σ J) : levU hσσ hJ hP g ∈ HR R σ J := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  show Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (levL (datR R σ J P T) (uT R σ J P g)
      (cj R σ (uI R σ J P g)))) * JR R J * LinearMap.toMatrix' (levL (datR R σ J P T)
      (uT R σ J P g) (cj R σ (uI R σ J P g))) = JR R J
  apply PI.LevelKSplit.W.SemiA.uj_of_uni
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  refine levL_uni H _ _ (fun b c => ?_) (fun b c => ?_) x y
  · calc ∑ a, sigR R σ (uT R σ J P g a b) * cj R σ (uI R σ J P g) a c
        = sigR R σ ((uI R σ J P g * uT R σ J P g) c b) := by
          rw [Matrix.mul_apply, map_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [cj_apply, map_mul, mul_comm]
      _ = if b = c then 1 else 0 := by
          rw [uI_mul_uT, Matrix.one_apply]
          by_cases h : b = c
          · subst h; simp
          · simp [h, Ne.symm h]
  · calc ∑ a, sigR R σ (cj R σ (uI R σ J P g) a b) * uT R σ J P g a c
        = (uI R σ J P g * uT R σ J P g) b c := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [cj_apply]
          exact congrArg (· * uT R σ J P g a c) (H.σσ _)
      _ = if b = c then 1 else 0 := by rw [uI_mul_uT, Matrix.one_apply]
end Hyp2
def levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (g : HA R σ J) :
    HA R σ J :=
  ⟨levU hσσ hJ hP g, levU_mem hσσ hJ hP g⟩
variable (R σ J P)
def Asub : Subgroup (HA R σ J) where
  carrier := {g | g ∈ Nsub R σ J P ∧ (∀ w ∈ Wp R σ J P, lin R σ J g w = w) ∧
    (∀ b, lin R σ J g (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ) ∧
    (∀ b, lin R σ J g⁻¹ (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ)}
  one_mem' := by
    refine ⟨(Nsub R σ J P).one_mem, fun w _ => lin_one R σ J w, fun b => ?_, fun b => ?_⟩
    · rw [lin_one]; exact Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩
    · rw [inv_one, lin_one]; exact Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
    obtain ⟨hh1, hh2, hh3, hh4⟩ := hh
    have key : ∀ (k : HA R σ J), (∀ b, lin R σ J k (ratV (F := F) R (P.f b)) ∈
        spanR (F := F) R P.f Set.univ) → ∀ y ∈ spanR (F := F) R P.f Set.univ,
        lin R σ J k y ∈ spanR (F := F) R P.f Set.univ := by
      intro k hk y hy
      have hle : spanR (F := F) R P.f Set.univ ≤ (spanR (F := F) R P.f Set.univ).comap (lin R σ J k) := by
        rw [spanR, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact hk b
      exact hle hy
    refine ⟨(Nsub R σ J P).mul_mem hg1 hh1, fun w hw => ?_, fun b => ?_, fun b => ?_⟩
    · rw [lin_mul, hh2 w hw, hg2 w hw]
    · rw [lin_mul]; exact key g hg3 _ (hh3 b)
    · rw [mul_inv_rev, lin_mul]; exact key h⁻¹ hh4 _ (hg4 b)
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
    refine ⟨(Nsub R σ J P).inv_mem hg1, fun w hw => ?_, hg4, fun b => ?_⟩
    · conv_lhs => rw [← hg2 w hw]
      exact lin_inv_lin R σ J g w
    · rw [inv_inv]; exact hg3 b
variable {R σ J P}
section Hyp3
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
end Hyp3
end R
end PI.LevelKSplit.W.NCL


