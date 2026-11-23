-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:12.941959+00:00
-- url     : https://prove2.me/theorems/38552641-e497-4ce9-820e-a54eb1d31bde
-- title:
--   First Kernel Explicit Formula
-- statement:
--   Definitions and structural lemmas for First Kernel Explicit Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_revIn_lt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_revIn_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_addBlock_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_blk_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_blk_app_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_blk_lt_length
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_revIn_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_revIn_app_lt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.A5x8
section GlobalTheory
variable {K : Type} [CommRing K] {m N : ℕ}
def eN (hN : N = m + 1) : Fin m ⊕ Unit ≃ Fin N :=
  ((Equiv.sumCongr (Equiv.refl (Fin m)) finOneEquiv.symm).trans finSumFinEquiv).trans
    (finCongr hN.symm)
theorem eN_inl (hN : N = m + 1) (a : Fin m) : ((eN hN (Sum.inl a) : Fin N) : ℕ) = a := by
  simp [eN]
theorem eN_inr (hN : N = m + 1) (u : Unit) : ((eN hN (Sum.inr u) : Fin N) : ℕ) = m := by
  simp [eN]
def blkM (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K) :
    Matrix (Fin N) (Fin N) K :=
  (fromBlocks A (replicateCol Unit b) (replicateRow Unit a) (Matrix.of fun _ _ => d)).submatrix
    (eN hN).symm (eN hN).symm
theorem blkM_ll (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (i j : Fin m) : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = A i j := by
  simp [blkM]
theorem blkM_lr (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (i : Fin m) (u : Unit) : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inr u)) = b i := by
  simp [blkM]
theorem blkM_rl (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (j : Fin m) (u : Unit) : blkM hN A b a d (eN hN (Sum.inr u)) (eN hN (Sum.inl j)) = a j := by
  simp [blkM]
theorem blkM_rr (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (u u' : Unit) : blkM hN A b a d (eN hN (Sum.inr u)) (eN hN (Sum.inr u')) = d := by
  simp [blkM]
theorem eq_blkM (hN : N = m + 1) (M : Matrix (Fin N) (Fin N) K) :
    M = blkM hN (Matrix.of fun i j => M (eN hN (Sum.inl i)) (eN hN (Sum.inl j)))
      (fun i => M (eN hN (Sum.inl i)) (eN hN (Sum.inr ())))
      (fun j => M (eN hN (Sum.inr ())) (eN hN (Sum.inl j)))
      (M (eN hN (Sum.inr ())) (eN hN (Sum.inr ()))) := by
  ext i j
  obtain ⟨x, rfl⟩ := (eN hN).surjective i
  obtain ⟨y, rfl⟩ := (eN hN).surjective j
  rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;> simp [blkM_ll, blkM_lr, blkM_rl, blkM_rr]
theorem blkM_inj (hN : N = m + 1) {A A' : Matrix (Fin m) (Fin m) K} {b a b' a' : Fin m → K}
    {d d' : K} (h : blkM hN A b a d = blkM hN A' b' a' d') :
    A = A' ∧ b = b' ∧ a = a' ∧ d = d' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inl j))
    simpa [blkM_ll] using this
  · funext i
    have := congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inr ()))
    simpa [blkM_lr] using this
  · funext j
    have := congrFun (congrFun h (eN hN (Sum.inr ()))) (eN hN (Sum.inl j))
    simpa [blkM_rl] using this
  · have := congrFun (congrFun h (eN hN (Sum.inr ()))) (eN hN (Sum.inr ()))
    simpa [blkM_rr] using this
theorem blkM_mul (hN : N = m + 1) (A A' : Matrix (Fin m) (Fin m) K) (b a b' a' : Fin m → K)
    (d d' : K) : blkM hN A b a d * blkM hN A' b' a' d' =
      blkM hN (A * A' + vecMulVec b a') (A *ᵥ b' + d' • b) (a ᵥ* A' + d • a') (a ⬝ᵥ b' + d * d') := by
  unfold blkM
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, mulVec, vecMul, dotProduct, vecMulVec, mul_comm]
theorem blkM_one (hN : N = m + 1) : blkM hN (1 : Matrix (Fin m) (Fin m) K) 0 0 1 = 1 := by
  ext i j
  obtain ⟨x, rfl⟩ := (eN hN).surjective i
  obtain ⟨y, rfl⟩ := (eN hN).surjective j
  rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;> simp [blkM_ll, blkM_lr, blkM_rl, blkM_rr, Matrix.one_apply]
theorem eN_lt_iff (hN : N = m + 1) (i j : Fin m) :
    eN hN (Sum.inl i) < eN hN (Sum.inl j) ↔ i < j := by
  rw [Fin.lt_iff_val_lt_val, eN_inl, eN_inl, Fin.lt_iff_val_lt_val]
theorem eN_inl_lt_inr (hN : N = m + 1) (i : Fin m) (u : Unit) :
    eN hN (Sum.inl i) < eN hN (Sum.inr u) := by
  rw [Fin.lt_iff_val_lt_val, eN_inl, eN_inr]
  exact i.isLt
theorem blkM_isLowUni (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K)
    (b a : Fin m → K) (d : K) : IsLowUni (blkM hN A b a d) ↔ IsLowUni A ∧ b = 0 ∧ d = 1 := by
  constructor
  · rintro ⟨hl, hd⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = 0 :=
        hl ((eN_lt_iff hN i j).2 hij)
      rwa [blkM_ll] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl i)) = 1 := hd _
      rwa [blkM_ll] at hh
    · funext i
      have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inr ())) = 0 :=
        hl (eN_inl_lt_inr hN i ())
      rwa [blkM_lr] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inr ())) (eN hN (Sum.inr ())) = 1 := hd _
      rwa [blkM_rr] at hh
  · rintro ⟨⟨hl, hd⟩, rfl, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : i < j := hij
      obtain ⟨x, rfl⟩ := (eN hN).surjective i
      obtain ⟨y, rfl⟩ := (eN hN).surjective j
      rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩
      · rw [blkM_ll]
        exact hl ((eN_lt_iff hN x y).1 hij')
      · rw [blkM_lr]; rfl
      · exact absurd hij' (lt_asymm (eN_inl_lt_inr hN y ()))
      · exact absurd hij' (lt_irrefl _)
    · obtain ⟨x, rfl⟩ := (eN hN).surjective i
      rcases x with x | ⟨⟩
      · rw [blkM_ll]
        exact hd x
      · rw [blkM_rr]
theorem blkM_isUpUni (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K)
    (b a : Fin m → K) (d : K) : IsUpUni (blkM hN A b a d) ↔ IsUpUni A ∧ a = 0 ∧ d = 1 := by
  constructor
  · rintro ⟨hl, hd⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = 0 :=
        hl ((eN_lt_iff hN j i).2 hij)
      rwa [blkM_ll] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl i)) = 1 := hd _
      rwa [blkM_ll] at hh
    · funext i
      have hh : blkM hN A b a d (eN hN (Sum.inr ())) (eN hN (Sum.inl i)) = 0 :=
        hl (eN_inl_lt_inr hN i ())
      rwa [blkM_rl] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inr ())) (eN hN (Sum.inr ())) = 1 := hd _
      rwa [blkM_rr] at hh
  · rintro ⟨⟨hl, hd⟩, rfl, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : j < i := hij
      obtain ⟨x, rfl⟩ := (eN hN).surjective i
      obtain ⟨y, rfl⟩ := (eN hN).surjective j
      rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩
      · rw [blkM_ll]
        exact hl ((eN_lt_iff hN y x).1 hij')
      · exact absurd hij' (lt_asymm (eN_inl_lt_inr hN x ()))
      · rw [blkM_rl]; rfl
      · exact absurd hij' (lt_irrefl _)
    · obtain ⟨x, rfl⟩ := (eN hN).surjective i
      rcases x with x | ⟨⟩
      · rw [blkM_ll]
        exact hd x
      · rw [blkM_rr]
def lastE (x : Fin m → K) : K := ∑ j : Fin m, if j.val + 1 = m then x j else 0
def bigZ (hN : N = m + 1) (Z : Matrix (Fin m) (Fin m) K) (ξ η : Fin m → K) (c : K) :
    Matrix (Fin N) (Fin N) K :=
  blkM hN Z (Z *ᵥ η) (ξ ᵥ* Z) (ξ ⬝ᵥ (Z *ᵥ η) + c)
end GlobalTheory
section Par
variable {K : Type} [CommRing K] (R : Subring K)
abbrev Par (h : Point K) : Type := Cos R h × (Fin h.1.sum → KR R) × (Fin h.1.sum → KR R)
def outV {m : ℕ} (x : Fin m → KR R) : Fin m → K := fun j => Quotient.out (x j)
theorem addBlock_sum (h : Point K) (c : Kˣ) : (addBlock h 1 c).1.sum = h.1.sum + 1 := by
  simp [addBlock]
def toCos {w : Point K} (p : lowW K w.1 w.2 × upUniG K w.1.sum) : Cos R w :=
  (Quotient.mk _ p.1, QuotientGroup.mk p.2)
open Classical in

def Gterm (ψ : AddChar K ℂ) (w w' : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum)
    (p' : lowW K w'.1 w'.2 × upUniG K w'.1.sum) : ℂ :=
  (if IsInt R (orbZ w p) ∧ IsInt R (orbZ w' p') then
    (Nat.card (isoZZ R (orbZ w p) (orbZ w' p')) : ℂ) else 0) * phase ψ p * conj (phase ψ p')
end Par
section SecPart
section SecBlk
variable {K : Type} [CommRing K] {m N : ℕ}
theorem sec_pt (h : Point K) (c : Kˣ) :
    pt (addBlock h 1 c).1 (addBlock h 1 c).2 =
      blkM (addBlock_sum h c) (pt h.1 h.2) 0 0 (c : K) := by
  ext x y
  obtain ⟨x, rfl⟩ := (eN (addBlock_sum h c)).surjective x
  obtain ⟨y, rfl⟩ := (eN (addBlock_sum h c)).surjective y
  rcases x with x | x <;> rcases y with y | y
  · rw [blkM_ll]
    simp only [pt, eN_inl]
    change (if (y : ℕ) = revIn (h.1 ++ [1]) x then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) x) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app_lt 1 _ _ x.2, A5x7.blk_app_lt 1 _ _ x.2,
      Function.update_of_ne (ne_of_lt (A5x7.blk_lt_length _ _ x.2))]
  · rw [blkM_lr]
    simp only [pt, eN_inl, eN_inr]
    change (if h.1.sum = revIn (h.1 ++ [1]) x then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) x) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app_lt 1 _ _ x.2, if_neg (ne_of_gt (Formalism.DoubleCosetMeasures.P.Phase.revIn_lt _ _ x.2))]
    rfl
  · rw [blkM_rl]
    simp only [pt, eN_inl, eN_inr]
    change (if (y : ℕ) = revIn (h.1 ++ [1]) h.1.sum then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) h.1.sum) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app _ 1 le_rfl, if_neg (by have := y.2; omega)]
    rfl
  · rw [blkM_rr]
    simp only [pt, eN_inr]
    change (if h.1.sum = revIn (h.1 ++ [1]) h.1.sum then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) h.1.sum) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app _ 1 le_rfl, A5x7.blk_app _ 1 le_rfl, if_pos (by omega), Function.update_self]
end SecBlk
section SecGrp
variable {K : Type} [CommRing K]
abbrev sec_m {n : ℕ} {H : Subgroup (GL (Fin n) K)} (g : H) : Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
def sec_gl {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (hx : x.det = 1) : GL (Fin n) K :=
  Matrix.nonsingInvUnit x (by rw [hx]; exact isUnit_one)
variable {m N : ℕ}
theorem sec_low_mem (h : Point K) (c : Kˣ) (A : Matrix (Fin h.1.sum) (Fin h.1.sum) K)
    (a : Fin h.1.sum → K) :
    (IsLowUni (blkM (addBlock_sum h c) A 0 a 1) ∧
      ∃ H : Matrix (Fin (addBlock h 1 c).1.sum) (Fin (addBlock h 1 c).1.sum) K, IsLowUni H ∧
        blkM (addBlock_sum h c) A 0 a 1 * pt (addBlock h 1 c).1 (addBlock h 1 c).2 =
          pt (addBlock h 1 c).1 (addBlock h 1 c).2 * H) ↔
    (IsLowUni A ∧ ∃ H : Matrix (Fin h.1.sum) (Fin h.1.sum) K, IsLowUni H ∧
      A * pt h.1 h.2 = pt h.1 h.2 * H) := by
  rw [sec_pt]
  constructor
  · rintro ⟨h1, H, hH, e⟩
    refine ⟨((blkM_isLowUni _ _ _ _ _).1 h1).1, ?_⟩
    rw [eq_blkM (addBlock_sum h c) H] at hH e
    refine ⟨_, ((blkM_isLowUni _ _ _ _ _).1 hH).1, ?_⟩
    rw [blkM_mul, blkM_mul] at e
    have := (blkM_inj _ e).1
    simpa using this
  · rintro ⟨h1, H, hH, e⟩
    refine ⟨(blkM_isLowUni _ _ _ _ _).2 ⟨h1, rfl, rfl⟩,
      blkM (addBlock_sum h c) H 0 (((c⁻¹ : Kˣ) : K) • (a ᵥ* pt h.1 h.2)) 1,
      (blkM_isLowUni _ _ _ _ _).2 ⟨hH, rfl, rfl⟩, ?_⟩
    rw [blkM_mul, blkM_mul]
    congr 1
    · simp [e]
    · simp
    · simp [smul_smul]
    · simp
def sec_lowJ (h : Point K) (c : Kˣ) (v : lowW K h.1 h.2) (ξ : Fin h.1.sum → K) :
    lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 :=
  ⟨sec_gl (blkM (addBlock_sum h c) (sec_m v) 0 (ξ ᵥ* sec_m v) 1)
    (isLowUni_det K ((blkM_isLowUni _ _ _ _ _).2 ⟨v.2.1, rfl, rfl⟩)),
    (sec_low_mem h c (sec_m v) (ξ ᵥ* sec_m v)).2 v.2⟩
def sec_upJ (h : Point K) (c : Kˣ) (u : upUniG K h.1.sum) (η : Fin h.1.sum → K) :
    upUniG K (addBlock h 1 c).1.sum :=
  ⟨sec_gl (blkM (addBlock_sum h c) (sec_m u) (sec_m u *ᵥ η) 0 1)
    (isUpUni_det K ((blkM_isUpUni _ _ _ _ _).2 ⟨u.2, rfl, rfl⟩)),
    (blkM_isUpUni _ _ _ _ _).2 ⟨u.2, rfl, rfl⟩⟩
end SecGrp
section SecFib
variable {K : Type} [CommRing K] (R : Subring K)
def sec_cX {m : ℕ} (x : Fin m → K) : Fin m → KR R := fun j => Submodule.Quotient.mk (x j)
end SecFib
section SecUp
variable {K : Type} [CommRing K] (R : Subring K)
def sec_sigma (h : Point K) (c : Kˣ) (t : Par R h) :
    lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum :=
  (sec_lowJ h c (rep R t.1).1 (outV R t.2.1), sec_upJ h c (rep R t.1).2 (outV R t.2.2))
end SecUp
end SecPart
section InvPart
variable {K : Type} [CommRing K] (R : Subring K)
end InvPart
section IsoPart
section IsoAbs
variable {K : Type} [CommRing K] (R : Subring K)
structure iso_Dat (M C : Type) [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C]
    (γ : Kˣ) (Φ : M →ₗ[R] K) (π : M →ₗ[R] C) (g : M) (lam : C →ₗ[R] KR R) : Prop where
  surj : Function.Surjective π
  ker : ∀ x, π x = 0 → ∃ r : R, x = r • g
  pg : π g = 0
  Pg : Φ g = (γ : K)
  lam_pi : ∀ x, lam (π x) = Submodule.Quotient.mk (((γ⁻¹ : Kˣ) : K) * Φ x)
variable {R}
variable {M₁ M₂ C₁ C₂ : Type} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂] {γ : Kˣ}
  {Φ₁ : M₁ →ₗ[R] K} {π₁ : M₁ →ₗ[R] C₁} {g₁ : M₁} {lam₁ : C₁ →ₗ[R] KR R}
  {Φ₂ : M₂ →ₗ[R] K} {π₂ : M₂ →ₗ[R] C₂} {g₂ : M₂} {lam₂ : C₂ →ₗ[R] KR R}
theorem iso_uniq (D : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁) {x y : M₁} (h1 : π₁ x = π₁ y)
    (h2 : Φ₁ x = Φ₁ y) : x = y := by
  obtain ⟨r, hr⟩ := D.ker (x - y) (by rw [map_sub, h1, sub_self])
  have h0 : Φ₁ (x - y) = 0 := by rw [map_sub, h2, sub_self]
  rw [hr, map_smul, D.Pg] at h0
  have hr0 : (r : K) = 0 := by
    have h3 : (r : K) * (γ : K) = 0 := h0
    exact (Units.mul_left_eq_zero γ).mp h3
  have hr1 : r = 0 := Subtype.ext hr0
  rw [hr1, zero_smul, sub_eq_zero] at hr
  exact hr
theorem iso_ex (D : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (y : C₂) (k : K)
    (h : lam₂ y = Submodule.Quotient.mk (((γ⁻¹ : Kˣ) : K) * k)) : ∃ x, π₂ x = y ∧ Φ₂ x = k := by
  obtain ⟨x0, hx0⟩ := D.surj y
  have h1 := D.lam_pi x0
  rw [hx0, h, Submodule.Quotient.eq, LinearMap.mem_range] at h1
  obtain ⟨s, hs⟩ := h1
  have hs' : (s : K) = ((γ⁻¹ : Kˣ) : K) * k - ((γ⁻¹ : Kˣ) : K) * Φ₂ x0 := hs
  refine ⟨x0 + s • g₂, by rw [map_add, map_smul, D.pg, smul_zero, add_zero, hx0], ?_⟩
  rw [map_add, map_smul, D.Pg]
  show Φ₂ x0 + (s : K) * (γ : K) = k
  rw [hs']
  have hγ : ((γ⁻¹ : Kˣ) : K) * (γ : K) = 1 := by simp
  linear_combination (k - Φ₂ x0) * hγ
def iso_liftFun (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) : M₂ :=
  Classical.choose (iso_ex D₂ (φ (π₁ x)) (Φ₁ x) (by rw [hφ, D₁.lam_pi]))
theorem iso_liftFun_spec (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂)
    (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) :
    π₂ (iso_liftFun D₂ D₁ φ hφ x) = φ (π₁ x) ∧ Φ₂ (iso_liftFun D₂ D₁ φ hφ x) = Φ₁ x := by
  unfold iso_liftFun
  exact Classical.choose_spec (iso_ex D₂ (φ (π₁ x)) (Φ₁ x) (by rw [hφ, D₁.lam_pi]))
def iso_lift (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) : M₁ →ₗ[R] M₂ where
  toFun := iso_liftFun D₂ D₁ φ hφ
  map_add' x y := by
    apply iso_uniq D₂
    · rw [map_add, (iso_liftFun_spec D₂ D₁ φ hφ _).1, (iso_liftFun_spec D₂ D₁ φ hφ _).1,
        (iso_liftFun_spec D₂ D₁ φ hφ _).1, map_add, map_add]
    · rw [map_add, (iso_liftFun_spec D₂ D₁ φ hφ _).2, (iso_liftFun_spec D₂ D₁ φ hφ _).2,
        (iso_liftFun_spec D₂ D₁ φ hφ _).2, map_add]
  map_smul' r x := by
    apply iso_uniq D₂
    · rw [RingHom.id_apply, map_smul, (iso_liftFun_spec D₂ D₁ φ hφ _).1,
        (iso_liftFun_spec D₂ D₁ φ hφ _).1, map_smul, map_smul]
    · rw [RingHom.id_apply, map_smul, (iso_liftFun_spec D₂ D₁ φ hφ _).2,
        (iso_liftFun_spec D₂ D₁ φ hφ _).2, map_smul]
theorem iso_lift_spec (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂)
    (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) :
    π₂ (iso_lift D₂ D₁ φ hφ x) = φ (π₁ x) ∧ Φ₂ (iso_lift D₂ D₁ φ hφ x) = Φ₁ x := by
  exact iso_liftFun_spec D₂ D₁ φ hφ x
theorem iso_symm_lam (φ : C₁ ≃ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (y : C₂) :
    lam₁ ((φ.symm : C₂ →ₗ[R] C₁) y) = lam₂ y := by
  rw [← hφ]
  simp
def iso_liftE (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ ≃ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) : M₁ ≃ₗ[R] M₂ :=
  LinearEquiv.ofLinearMap (iso_lift D₂ D₁ (φ : C₁ →ₗ[R] C₂) hφ)
    (iso_lift D₁ D₂ (φ.symm : C₂ →ₗ[R] C₁) (iso_symm_lam φ hφ))
    (by
      ext x
      apply iso_uniq D₂
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₂ D₁ _ _ _).1, (iso_lift_spec D₁ D₂ _ _ _).1]
        simp
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₂ D₁ _ _ _).2, (iso_lift_spec D₁ D₂ _ _ _).2])
    (by
      ext x
      apply iso_uniq D₁
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₁ D₂ _ _ _).1, (iso_lift_spec D₂ D₁ _ _ _).1]
        simp
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₁ D₂ _ _ _).2, (iso_lift_spec D₂ D₁ _ _ _).2])
end IsoAbs
section IsoBlk
variable {K : Type} [CommRing K] {m N : ℕ} (hN : N = m + 1)
def iso_vec {X : Type} (a : Fin m → X) (r : X) : Fin N → X :=
  fun x => Sum.elim a (fun _ => r) ((eN hN).symm x)
theorem iso_vec_inl {X : Type} (a : Fin m → X) (r : X) (i : Fin m) :
    iso_vec hN a r (eN hN (Sum.inl i)) = a i := by
  simp [iso_vec]
theorem iso_vec_inr {X : Type} (a : Fin m → X) (r : X) (u : Unit) :
    iso_vec hN a r (eN hN (Sum.inr u)) = r := by
  simp [iso_vec]
theorem iso_vec_eta {X : Type} (x : Fin N → X) :
    iso_vec hN (fun i => x (eN hN (Sum.inl i))) (x (eN hN (Sum.inr ()))) = x := by
  funext z
  obtain ⟨w, rfl⟩ := (eN hN).surjective z
  rcases w with i | ⟨⟩
  · exact iso_vec_inl hN _ _ i
  · exact iso_vec_inr hN _ _ ()
theorem iso_vec_ext {X : Type} {x y : Fin N → X}
    (h1 : ∀ i, x (eN hN (Sum.inl i)) = y (eN hN (Sum.inl i)))
    (h2 : x (eN hN (Sum.inr ())) = y (eN hN (Sum.inr ()))) : x = y := by
  funext z
  obtain ⟨w, rfl⟩ := (eN hN).surjective z
  rcases w with i | ⟨⟩
  · exact h1 i
  · exact h2
theorem iso_blkM_mulVec (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (y : Fin m → K) (s : K) :
    blkM hN A b a d *ᵥ iso_vec hN y s = iso_vec hN (A *ᵥ y + s • b) (a ⬝ᵥ y + d * s) := by
  apply iso_vec_ext hN
  · intro i
    rw [iso_vec_inl]
    simp only [mulVec, dotProduct]
    rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
    simp [blkM_ll, blkM_lr, iso_vec_inl, iso_vec_inr, mulVec, dotProduct, mul_comm]
  · rw [iso_vec_inr]
    simp only [mulVec, dotProduct]
    rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
    simp [blkM_rl, blkM_rr, iso_vec_inl, iso_vec_inr, dotProduct]
theorem iso_bigZ_mul_inv (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K)
    (c : Kˣ) : bigZ hN Z ξ η (c : K) *
      blkM hN (Z⁻¹ + vecMulVec η (((c⁻¹ : Kˣ) : K) • ξ)) (-(((c⁻¹ : Kˣ) : K) • η))
        (-(((c⁻¹ : Kˣ) : K) • ξ)) ((c⁻¹ : Kˣ) : K) = 1 := by
  set ci : K := ((c⁻¹ : Kˣ) : K) with hci
  have hZi : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hZ
  have hZi' : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hc : (c : K) * ci = 1 := by simp [hci]
  have hmv : ∀ w : Fin m → K, Z * vecMulVec η w = vecMulVec (Z *ᵥ η) w := by
    intro w
    ext i j
    simp [vecMulVec, Matrix.mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  have hv : ∀ (x w : Fin m → K), x ᵥ* vecMulVec η w = (x ⬝ᵥ η) • w := by
    intro x w
    funext j
    simp [vecMul, vecMulVec, dotProduct, Finset.sum_mul, mul_assoc]
  suffices H : (Z * (Z⁻¹ + vecMulVec η (ci • ξ)) + vecMulVec (Z *ᵥ η) (-(ci • ξ)) = 1) ∧
      (Z *ᵥ -(ci • η) + ci • (Z *ᵥ η) = 0) ∧
      ((ξ ᵥ* Z) ᵥ* (Z⁻¹ + vecMulVec η (ci • ξ)) + (ξ ⬝ᵥ (Z *ᵥ η) + (c : K)) • -(ci • ξ) = 0) ∧
      ((ξ ᵥ* Z) ⬝ᵥ -(ci • η) + (ξ ⬝ᵥ (Z *ᵥ η) + (c : K)) * ci = 1) by
    unfold bigZ
    rw [blkM_mul, H.1, H.2.1, H.2.2.1, H.2.2.2, blkM_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_add, hZi, hmv, add_assoc]
    have h0 : vecMulVec (Z *ᵥ η) (ci • ξ) + vecMulVec (Z *ᵥ η) (-(ci • ξ)) = 0 := by
      ext i j
      simp [vecMulVec]
    rw [h0, add_zero]
  · rw [Matrix.mulVec_neg, Matrix.mulVec_smul]
    simp
  · rw [Matrix.vecMul_add, Matrix.vecMul_vecMul, hZi, Matrix.vecMul_one, hv, ← Matrix.dotProduct_mulVec]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination (-(ξ j)) * hc
  · rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul,
      smul_eq_mul]
    linear_combination hc
theorem iso_bigZ_det (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K)
    (c : Kˣ) : IsUnit (bigZ hN Z ξ η (c : K)).det := by
  exact Matrix.isUnit_det_of_right_inverse (iso_bigZ_mul_inv hN Z hZ ξ η c)
end IsoBlk
section IsoConc
variable {K : Type} [CommRing K] (R : Subring K) {m N : ℕ} (hN : N = m + 1)
theorem iso_coeLin_vec (a : Fin m → R) (r : R) :
    coeLin R (iso_vec hN a r) = iso_vec hN (coeLin R a) (r : K) := by
  funext z
  obtain ⟨w, rfl⟩ := (eN hN).surjective z
  rcases w with i | ⟨⟩ <;> (simp [coeLin, iso_vec_inl, iso_vec_inr]; try rfl)
def iso_top : (Fin N → R) →ₗ[R] (Fin m → R) :=
  LinearMap.funLeft R R (fun i => eN hN (Sum.inl i))
def iso_bot : (Fin N → R) →ₗ[R] R := LinearMap.proj (eN hN (Sum.inr ()))
theorem iso_eta (x : Fin N → R) : iso_vec hN (iso_top R hN x) (iso_bot R hN x) = x := by
  exact iso_vec_eta hN x
def iso_dot (ξ : Fin m → K) : (Fin m → R) →ₗ[R] K where
  toFun v := ξ ⬝ᵥ coeLin R v
  map_add' v w := by rw [map_add, dotProduct_add]
  map_smul' r v := by
    rw [map_smul, RingHom.id_apply]
    have : r • coeLin R v = (r : K) • coeLin R v := rfl
    rw [this, dotProduct_smul]; rfl
def affineForm (ξ : Fin m → K) : (Fin N → R) →ₗ[R] K :=
  (Algebra.linearMap R K).comp (iso_bot R hN) - (iso_dot R ξ).comp (iso_top R hN)
theorem affine_form_apply (ξ : Fin m → K) (x : Fin N → R) :
    affineForm R hN ξ x = (iso_bot R hN x : K) - ξ ⬝ᵥ coeLin R (iso_top R hN x) := rfl
def iso_rho (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : (Fin N → R) →ₗ[R] coker R Z × K :=
  LinearMap.prod ((Submodule.mkQ _).comp (iso_top R hN)) (affineForm R hN ξ)
theorem iso_mem_ker (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) (x : Fin N → R) :
    x ∈ LinearMap.ker (iso_rho R hN Z ξ) ↔ iso_top R hN x ∈ latZ R Z ∧ affineForm R hN ξ x = 0 := by
  simp [iso_rho, LinearMap.mem_ker, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
abbrev iso_M (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : Type :=
  (Fin N → R) ⧸ LinearMap.ker (iso_rho R hN Z ξ)
def iso_Phi (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : iso_M R hN Z ξ →ₗ[R] K :=
  (LinearMap.ker (iso_rho R hN Z ξ)).liftQ (affineForm R hN ξ)
    (fun x hx => ((iso_mem_ker R hN Z ξ x).1 hx).2)
def iso_piS (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : iso_M R hN Z ξ →ₗ[R] coker R Z :=
  (LinearMap.ker (iso_rho R hN Z ξ)).liftQ ((Submodule.mkQ _).comp (iso_top R hN))
    (fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ((iso_mem_ker R hN Z ξ x).1 hx).1)
theorem iso_ker_le (Z : Matrix (Fin m) (Fin m) K) (ξ η : Fin m → K) (c : K) :
    LinearMap.ker (iso_rho R hN Z ξ) ≤ LinearMap.ker (Submodule.mkQ (latZ R (bigZ hN Z ξ η c))) := by
  intro x hx
  rw [iso_mem_ker] at hx
  obtain ⟨hlat, hphi⟩ := hx
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨u, hu⟩ := hlat
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hu
  rw [affine_form_apply, sub_eq_zero] at hphi
  refine ⟨iso_vec hN u 0, ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  rw [iso_coeLin_vec, bigZ, iso_blkM_mulVec, ← iso_eta R hN x, iso_coeLin_vec, hphi,
    ← hu, ← Matrix.dotProduct_mulVec]
  simp
def iso_piB (Z : Matrix (Fin m) (Fin m) K) (ξ η : Fin m → K) (c : K) :
    iso_M R hN Z ξ →ₗ[R] coker R (bigZ hN Z ξ η c) :=
  (LinearMap.ker (iso_rho R hN Z ξ)).liftQ (Submodule.mkQ _) (iso_ker_le R hN Z ξ η c)
end IsoConc
section IsoData
variable {K : Type} [CommRing K] (R : Subring K) {m N : ℕ} (hN : N = m + 1)
  (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K) (c : Kˣ)
end IsoData
end IsoPart
section Dual
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}
def iA (Z : Matrix (Fin m) (Fin m) K) (α : coker R Z →ₗ[R] KR R) : Fin m → KR R :=
  fun j => α (Submodule.Quotient.mk (Pi.single j 1))
def iC (Z : Matrix (Fin m) (Fin m) K) (β : coker R Z) : Fin m → KR R :=
  fun j => A5x3.rowFun R Z j (Quotient.out β)
end Dual
section Comb
end Comb
section Inner
variable {K : Type} [CommRing K]
open Classical in

def tTerm (R : Subring K) (ψ : AddChar K ℂ) {m m' N N' : ℕ} (hN : N = m + 1) (hN' : N' = m' + 1)
    (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K) (c : K)
    (y : ((Fin m → KR R) × (Fin m → KR R)) × ((Fin m' → KR R) × (Fin m' → KR R))) : ℂ :=
  (if IsInt R (bigZ hN Z₁ (outV R y.1.1) (outV R y.1.2) c) ∧
      IsInt R (bigZ hN' Z₂ (outV R y.2.1) (outV R y.2.2) c) then
    (Nat.card (isoZZ R (bigZ hN Z₁ (outV R y.1.1) (outV R y.1.2) c)
      (bigZ hN' Z₂ (outV R y.2.1) (outV R y.2.2) c)) : ℂ) else 0) *
    ψ (lastE (outV R y.1.1) + lastE (outV R y.1.2)) *
    conj (ψ (lastE (outV R y.2.1) + lastE (outV R y.2.2)))
def iota (R : Subring K) {m m' : ℕ} (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K)
    (s : ((coker R Z₁ →ₗ[R] KR R) × coker R Z₁) × ((coker R Z₂ →ₗ[R] KR R) × coker R Z₂)) :
    ((Fin m → KR R) × (Fin m → KR R)) × ((Fin m' → KR R) × (Fin m' → KR R)) :=
  ((iA R Z₁ s.1.1, iC R Z₁ s.1.2), (iA R Z₂ s.2.1, iC R Z₂ s.2.2))
end Inner
section InnerSum
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
end InnerSum
section Final
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
end Final
end Formalism.FourierDecayAlt.P.A5x8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


