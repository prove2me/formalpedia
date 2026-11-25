-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:30.078346+00:00
-- url     : https://prove2.me/theorems/d4d5f462-78cf-4204-ae52-1b967e06f65b
-- title:
--   To Matrix Lin
-- statement:
--   Definitions and structural lemmas for To Matrix Lin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_Pi_comp
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_Pi_uni
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_mapW_of_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
section R
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
theorem uj_of_uni {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σA : A →+* A)
    (JA : Matrix n n A) (Mx : Matrix n n A)
    (h : ∀ x y, Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y) = Formalism.UG.hform σA JA x y) :
    Formalism.UG.cT σA Mx * JA * Mx = JA := by
  classical
  ext a b
  have hcol : ∀ c, Mx.mulVec (Pi.single c (1 : A)) = fun i => Mx i c := by
    intro c
    funext i
    rw [Matrix.mulVec_single]
    simp
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [hcol, hcol] at h1
  simp only [Formalism.UG.hform] at h1
  rw [show (Formalism.UG.cT σA Mx * JA * Mx) a b = ∑ i, ∑ j, σA (Mx i a) * JA i j * Mx j b by
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm], h1]
  have hs : ∀ i, σA ((Pi.single a (1 : A) : n → A) i) = (Pi.single a (1 : A) : n → A) i := by
    intro i
    by_cases hi : i = a
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  simp only [hs]
  simp [Pi.single_apply]
def piMat (g : HA R σ J) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  LinearMap.toMatrix' ((datR R σ J P T).Pi (lin R σ J g))
theorem piMat_mulVec (g : HA R σ J) (v : Fin M → R ⊗[F] E) :
    Matrix.mulVec (piMat (P := P) (T := T) g) v = (datR R σ J P T).Pi (lin R σ J g) v := by
  unfold piMat
  exact LinearMap.toMatrix'_mulVec _ _
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
theorem spanR_of_last_not_mem (s : Set (Fin (r + 1))) (hs : Fin.last r ∉ s) :
    spanR (F := F) R (F0 P) s ≤ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  unfold spanR
  refine Submodule.span_le.mpr ?_
  rintro x ⟨b, hb, rfl⟩
  refine Submodule.subset_span ?_
  induction b using Fin.lastCases with
  | last => exact absurd hb hs
  | cast b' => exact ⟨b', by simp [F0, datR]⟩
theorem mapX_lin_of_mem_Ssub {g : HA R σ J} (hg : g ∈ Ssub R σ J P) :
    (datR R σ J P T).MapX (lin R σ J g) := by
  intro a
  have key := (show UniC R σ J (F0 P) g from hg) (Fin.castSucc a)
  have hle := spanR_of_last_not_mem (R := R) (σ := σ) (J := J) (P := P) (T := T) hσσ hJ hP {b | b < Fin.castSucc a}
    (fun h => lt_asymm h (Fin.castSucc_lt_last a))
  have h2 := Submodule.add_mem _ (hle key)
    (Submodule.subset_span (⟨a, rfl⟩ : (datR R σ J P T).e a ∈ Set.range (datR R σ J P T).e))
  have hF : ratV (F := F) R (F0 P (Fin.castSucc a)) = (datR R σ J P T).e a := by
    simp [F0, datR]
  rw [hF, sub_add_cancel] at h2
  exact h2
theorem mapW_lin_of_mem_Ssub {g : HA R σ J} (hg : g ∈ Ssub R σ J P) :
    (datR R σ J P T).MapW (lin R σ J g) := by
  have hgi : g⁻¹ ∈ Ssub R σ J P := (Ssub R σ J P).inv_mem hg
  refine SemiG.Dat.mapW_of_inv (D := datR R σ J P T) (Si := lin R σ J g⁻¹)
    (fun v => by rw [lin_lin_inv]) (fun x y => by
      show hR R σ J (lin R σ J g x) (lin R σ J g y) = hR R σ J x y
      rw [hR_lin]) (mapX_lin_of_mem_Ssub hσσ hJ hP hgi) ?_
  have key := (show UniC R σ J (F0 P) g⁻¹ from hgi) (Fin.last r)
  have hle := spanR_of_last_not_mem (R := R) (σ := σ) (J := J) (P := P) (T := T) hσσ hJ hP {b | b < Fin.last r}
    (fun h => lt_irrefl (Fin.last r) h)
  have hF : ratV (F := F) R (F0 P (Fin.last r)) = (datR R σ J P T).z := by
    simp [F0, datR]
  rw [hF] at key
  exact hle key
theorem Pi_lin_mul {g g' : HA R σ J} (hg : g ∈ Ssub R σ J P) (hg' : g' ∈ Ssub R σ J P) :
    (datR R σ J P T).Pi (lin R σ J (g * g')) =
      (datR R σ J P T).Pi (lin R σ J g) ∘ₗ (datR R σ J P T).Pi (lin R σ J g') := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, SemiG.Dat.Pi_comp (D := datR R σ J P T) (datR_hyp hσσ hJ hP)
    (mapX_lin_of_mem_Ssub hσσ hJ hP hg) (mapW_lin_of_mem_Ssub hσσ hJ hP hg')]
  have hl : lin R σ J (g * g') = lin R σ J g ∘ₗ lin R σ J g' :=
    LinearMap.ext fun x => by rw [lin_mul]; rfl
  rw [hl]
theorem Pi_lin_one : (datR R σ J P T).Pi (lin R σ J 1) = LinearMap.id := by
  classical
  have hsym : ∀ x y : Fin M → E, hE σ J y x = σ (hE σ J x y) := by
    intro x y
    unfold hE Formalism.UG.hform
    simp only [map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσσ, hJ.1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRrat : ∀ x y : Fin M → E, (datR R σ J P T).hL (ratV (F := F) R x) (ratV (F := F) R y) =
      inclR (F := F) R (hE σ J x y) := by
    intro x y
    show (datR R σ J P T).h (ratV (F := F) R x) (ratV (F := F) R y) = _
    unfold SemiG.Dat.h datR ratV hE Formalism.UG.hform sigR JR inclR
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_sum,
      map_mul]
  have hee : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).e a) = 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R (P.e a)) = 0
    rw [hRrat, hP.1 b a, map_zero]
  have hff : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).f a) = 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R (P.f a)) = 0
    rw [hRrat, hP.2.1 b a, map_zero]
  have hef : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).f a) = if b = a then 1 else 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R (P.f a)) = _
    rw [hRrat, hP.2.2.1 b a]
    split_ifs <;> simp
  have hfe : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).e a) = if b = a then 1 else 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R (P.e a)) = _
    rw [hRrat, hsym, hP.2.2.1 a b]
    by_cases h : b = a
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
      simp
  have hez : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).e b) (datR R σ J P T).z = 0 := by
    intro b
    show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R P.z) = 0
    rw [hRrat, hP.2.2.2.1 b, map_zero]
  have hfz : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).f b) (datR R σ J P T).z = 0 := by
    intro b
    show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R P.z) = 0
    rw [hRrat, hP.2.2.2.2.1 b, map_zero]
  have hze : ∀ a, (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).e a) = 0 := by
    intro a
    show (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R (P.e a)) = 0
    rw [hRrat, hsym, hP.2.2.2.1 a, map_zero, map_zero]
  have hzf : ∀ a, (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).f a) = 0 := by
    intro a
    show (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R (P.f a)) = 0
    rw [hRrat, hsym, hP.2.2.2.2.1 a, map_zero, map_zero]
  have hzz : (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z (datR R σ J P T).z = 1 := by
    show inclR (F := F) R ((algebraMap F E (-T))⁻¹) *
      (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
    rw [hRrat, hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀, map_one]
    exact (map_ne_zero _).mpr (neg_ne_zero.mpr hP.2.2.2.2.2.2)
  have hpU : ∀ u, (datR R σ J P T).pU u = ∑ a, (datR R σ J P T).hL ((datR R σ J P T).f a) u • (datR R σ J P T).e a + ∑ a, (datR R σ J P T).hL ((datR R σ J P T).e a) u • (datR R σ J P T).f a +
      ((datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z u) • (datR R σ J P T).z := by
    intro u
    simp only [SemiG.Dat.pU, SemiG.Dat.pX, SemiG.Dat.pXv, SemiG.Dat.pz, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      smul_eq_mul]
  have key : ∀ v, (datR R σ J P T).pU ((datR R σ J P T).pU v) = (datR R σ J P T).pU v := by
    intro v
    have c1 : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).pU v) = (datR R σ J P T).hL ((datR R σ J P T).f b) v := by
      intro b
      rw [hpU v]
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hfe b, hff b, hfz b]
      simp
    have c2 : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).pU v) = (datR R σ J P T).hL ((datR R σ J P T).e b) v := by
      intro b
      rw [hpU v]
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hee b, hef b, hez b]
      simp
    have c3 : (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).pU v) = (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z v := by
      rw [hpU v]
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hze, hzf, mul_zero,
        Finset.sum_const_zero, zero_add]
      linear_combination ((datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z v) * hzz
    rw [hpU ((datR R σ J P T).pU v), c3]
    simp only [c1, c2]
    exact (hpU v).symm
  have hid : lin R σ J 1 = LinearMap.id := by
    apply LinearMap.ext
    intro v
    unfold lin
    show (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVecLin v = v
    rw [Matrix.mulVecLin_apply, Matrix.one_mulVec]
  unfold SemiG.Dat.Pi
  rw [hid, LinearMap.id_comp]
  unfold SemiG.Dat.pW
  apply LinearMap.ext
  intro v
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, key]
  abel
def piU (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : GL (Fin M) (R ⊗[F] E) where
  val := piMat (P := P) (T := T) g
  inv := piMat (P := P) (T := T) g⁻¹
  val_inv := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP hg ((Ssub R σ J P).inv_mem hg), mul_inv_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]
  inv_val := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP ((Ssub R σ J P).inv_mem hg) hg, inv_mul_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]
theorem uni_lin' (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := by
  intro x y
  show hR R σ J (lin R σ J g x) (lin R σ J g y) = hR R σ J x y
  rw [hR_lin]
theorem piU_mem (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : piU hσσ hJ hP g hg ∈ HR R σ J := by
  have hU := SemiG.Dat.Pi_uni (D := datR R σ J P T) (datR_hyp hσσ hJ hP)
    (mapW_lin_of_mem_Ssub hσσ hJ hP hg) (uni_lin' hσσ hJ hP g)
  have hm := uj_of_uni (sigR R σ) (JR R J) (piMat (P := P) (T := T) g) (fun x y => by
    rw [piMat_mulVec, piMat_mulVec]
    exact hU x y)
  exact hm
def piG (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : HA R σ J :=
  ⟨piU hσσ hJ hP g hg, piU_mem hσσ hJ hP g hg⟩
end R
end PI.LevelKSplit.W.SemiA


