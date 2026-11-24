-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:39.669819+00:00
-- url     : https://prove2.me/theorems/9d555ef1-27e9-4800-8ae2-61c5ed7c367f
-- title:
--   Wm Mul Wm Comm
-- statement:
--   Definitions and structural lemmas for Wm Mul Wm Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/WmMulWmComm.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_cartan
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_CountingSumsFrames_eul_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_mem
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_FockB_pderiv_mem
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_pderiv_comm
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_glAct_X
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_ProjS_coeff_eulL
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_Uop_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_disj_last
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_comm_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames MvPolynomial Finset
section Gen
variable {p : ℕ} [Fact p.Prime] {σ : Type} {n : ℕ}
noncomputable def compW (p : ℕ) [Fact p.Prime] (w : (σ →₀ ℕ) → Fin n → ℤ) (μ : Fin n → ℤ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] where
  toFun x := compP (fun m => w m = μ) x
  map_add' x y := by
    ext m; simp only [coeff_compP, coeff_add]; split_ifs <;> simp
  map_smul' a x := by
    ext m; simp only [coeff_compP, coeff_smul, RingHom.id_apply]; split_ifs <;> simp
theorem coeff_compW (w : (σ →₀ ℕ) → Fin n → ℤ) (μ : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) :
    coeff m (compW p w μ x) = if w m = μ then coeff m x else 0 := by
  show coeff m (compP _ x) = _
  rw [coeff_compP]
  split_ifs <;> rfl
theorem compW_fix (w : (σ →₀ ℕ) → Fin n → ℤ) (μ ν : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p])
    (hx : ∀ m, coeff m x ≠ 0 → w m = ν) : compW p w μ x = if ν = μ then x else 0 := by
  ext m
  rw [coeff_compW]
  by_cases h0 : coeff m x = 0
  · split_ifs <;> simp [h0]
  · rw [hx m h0]
    split_ifs <;> simp
theorem compW_isW (w : (σ →₀ ℕ) → Fin n → ℤ) (μ : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) :
    ∀ m, coeff m (compW p w μ x) ≠ 0 → w m = μ := by
  intro m hm
  rw [coeff_compW] at hm
  by_contra h
  exact hm (if_neg h)
theorem sum_compW (w : (σ →₀ ℕ) → Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) (S : Finset (Fin n → ℤ))
    (hS : ∀ μ ∉ S, compW p w μ x = 0) : ∑ μ ∈ S, compW p w μ x = x := by
  ext d
  rw [coeff_sum]
  simp only [coeff_compW]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have := congrArg (coeff d) (hS _ h)
    rw [coeff_compW, if_pos rfl, coeff_zero] at this
    exact this.symm
theorem compW_dec (w : (σ →₀ ℕ) → Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) :
    ∀ μ ∉ x.support.image w, compW p w μ x = 0 := by
  intro μ hμ
  ext m
  rw [coeff_compW, coeff_zero]
  split_ifs with h
  · by_contra hne
    exact hμ (Finset.mem_image.mpr ⟨m, mem_support_iff.mpr hne, h⟩)
  · rfl
theorem isW_E (E : Fin n → Fin n → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (w : (σ →₀ ℕ) → Fin n → ℤ)
    (hcomm : ∀ a b c d x, E a b (E c d x) - E c d (E a b x) =
      (if b = c then E a d x else 0) - (if d = a then E c b x else 0))
    (hdiag : ∀ c x m, coeff m (E c c x) = ((w m c : ℤ) : ℚ_[p]) * coeff m x)
    (a b : Fin n) (μ : Fin n → ℤ) (x : MvPolynomial σ ℚ_[p]) (hx : ∀ m, coeff m x ≠ 0 → w m = μ) :
    ∀ m, coeff m (E a b x) ≠ 0 → w m = μ + dl a b := by
  intro m hm
  funext c
  have h1 : E c c x = ((μ c : ℤ) : ℚ_[p]) • x := by
    ext m'
    rw [hdiag, coeff_smul, smul_eq_mul]
    by_cases h0 : coeff m' x = 0
    · rw [h0, mul_zero, mul_zero]
    · rw [hx m' h0]
  have h2 := congrArg (coeff m) (hcomm c c a b x)
  rw [h1, map_smul, coeff_sub, hdiag, coeff_smul, smul_eq_mul, coeff_sub] at h2
  have h3 : coeff m (if c = a then E c b x else 0) = (if c = a then 1 else 0) * coeff m (E a b x) := by
    split_ifs with h
    · subst h; rw [one_mul]
    · simp
  have h4 : coeff m (if b = c then E a c x else 0) = (if c = b then 1 else 0) * coeff m (E a b x) := by
    by_cases h : b = c
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  rw [h3, h4, ← sub_mul, ← sub_mul] at h2
  have h5 := mul_right_cancel₀ hm h2
  rw [Pi.add_apply, dl_apply]
  have h6 : ((w m c - μ c : ℤ) : ℚ_[p]) =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℤ) : ℚ_[p]) := by
    push_cast; exact h5
  have := Int.cast_injective h6
  omega
noncomputable def mkGlW (E : Fin n → Fin n → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (w : (σ →₀ ℕ) → Fin n → ℤ)
    (hcomm : ∀ a b c d x, E a b (E c d x) - E c d (E a b x) =
      (if b = c then E a d x else 0) - (if d = a then E c b x else 0))
    (hdiag : ∀ c x m, coeff m (E c c x) = ((w m c : ℤ) : ℚ_[p]) * coeff m x) :
    GlW ℚ_[p] (MvPolynomial σ ℚ_[p]) n where
  E := E
  comm := hcomm
  comp := compW p w
  dec := fun x => ⟨x.support.image w, compW_dec w x⟩
  sum_comp := fun x S hS => sum_compW w x S hS
  idem := fun μ ν x => by
    rw [compW_fix w μ ν _ (compW_isW w ν x)]
    by_cases h : μ = ν
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  diag := fun c μ x => by
    ext m
    rw [hdiag, coeff_smul, smul_eq_mul, coeff_compW]
    split_ifs with h
    · rw [h]
    · simp
  shift := fun a b μ x => by
    conv_lhs => rw [← sum_compW w x _ (compW_dec w x)]
    rw [map_sum, map_sum]
    have e' : ∀ ν, compW p w μ (E a b (compW p w ν x)) =
        if ν = μ - dl a b then E a b (compW p w ν x) else 0 := by
      intro ν
      rw [compW_fix w μ (ν + dl a b) _ (isW_E E w hcomm hdiag a b ν _ (compW_isW w ν x))]
      congr 1
      apply propext; constructor <;> intro h <;> subst h <;> simp
    simp only [e', Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [compW_dec w x _ h, map_zero]
end Gen
section Rel
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
noncomputable def Aop (p : ℕ) [Fact p.Prime] (K r : ℕ) (c : ℤ) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  ((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K r
theorem Aop_apply (c : ℤ) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Aop p K r c F = ((c : ℤ) : ℚ_[p]) • F - ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F := rfl
theorem dW_apply (j : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    dW p K j F = pderiv (Fin.last K, j) F := rfl
theorem pderiv_X_mul (j b : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, j) (X (Fin.last K, b) * G) =
      (if j = b then G else 0) + X (Fin.last K, b) * pderiv (Fin.last K, j) G := by
  classical
  rw [pderiv_mul, pderiv_X]
  by_cases h : j = b
  · subst h; simp
  · have h' : ((Fin.last K, b) : Fin (K + 1) × Fin r) ≠ (Fin.last K, j) := fun h' => h (Prod.mk.inj h').2.symm
    rw [Pi.single_apply, if_neg h', if_neg h, zero_mul]
theorem glJ_X_mul (LL : Letters (K + 1)) (a b d : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL K a b (X (Fin.last K, d) * G) = X (Fin.last K, d) * glAct p LL K a b G := by
  have h2 : ¬ ((Fin.last K : Fin (K + 1)) : ℕ) < K := by simp
  rw [glAct_mul, glAct_X, if_neg h2, zero_mul, zero_add]
theorem pderiv_glJ (LL : Letters (K + 1)) (a b d : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, d) (glAct p LL K a b x) = glAct p LL K a b (pderiv (Fin.last K, d) x) :=
  FockB.ops_apply_comm disj_last (FockB.pderiv_mem (last_mem d)) (glAct_mem LL K a b) x
theorem eul_X_mul (b : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (X (Fin.last K, b) * G) =
      X (Fin.last K, b) * G + X (Fin.last K, b) * ProjS.eulL (fun c : Fin r => (Fin.last K, c)) G := by
  rw [ProjS.eulL_apply, ProjS.eulL_apply]
  simp only [pderiv_X_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ b), Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring
theorem pderiv_eul (j : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    pderiv (Fin.last K, j) (ProjS.eulL (fun c : Fin r => (Fin.last K, c)) G) =
      pderiv (Fin.last K, j) G + ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (pderiv (Fin.last K, j) G) := by
  rw [ProjS.eulL_apply, ProjS.eulL_apply, map_sum]
  simp only [pderiv_X_mul, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [ProjS.pderiv_comm]
theorem eul_Uop (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (Uop p LL c Cs i F) =
      Uop p LL c Cs i F + Uop p LL c Cs i (ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F) := by
  rw [Uop_apply, Uop_apply, map_sub, map_sum]
  simp only [eul_X_mul, eul_glAct, map_sub, map_smul, Finset.sum_add_distrib]
  abel
theorem A_U (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Aop p K r c (Uop p LL c Cs i F) - Uop p LL c Cs i (Aop p K r c F) = -Uop p LL c Cs i F := by
  rw [Aop_apply, Aop_apply, eul_Uop, map_sub, map_smul]
  abel
theorem A_d (c : ℤ) (j : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Aop p K r c (dW p K j F) - dW p K j (Aop p K r c F) = dW p K j F := by
  rw [Aop_apply, Aop_apply, dW_apply, dW_apply, map_sub, Derivation.map_smul, pderiv_eul]
  abel
theorem e_A (LL : Letters (K + 1)) (c : ℤ) (a b : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) a b (Aop p K r c F) - Aop p K r c (glAct p LL (K + 1) a b F) = 0 := by
  rw [Aop_apply, Aop_apply, eul_glAct, map_sub, map_smul]
  abel
theorem d_U (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : ℤ) (Cs : Finset (Fin r)) (i j : Fin r)
    (hj : j ∈ Cs) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    dW p K j (Uop p LL c Cs i F) - Uop p LL c Cs i (dW p K j F) =
      (if j = i then Aop p K r c F else 0) - glAct p LL (K + 1) i j F := by
  rw [dW_apply, dW_apply, Uop_apply, Uop_apply, map_sub, map_sum, Aop_apply, glAct_succ LL hv]
  simp only [pderiv_X_mul, pderiv_glJ, map_sub, Derivation.map_smul, pderiv_eul, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, if_pos hj]
  simp only [mul_sub, mul_add]
  abel
noncomputable def Sop (p : ℕ) [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r) :
    Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  ∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b
theorem Sop_apply (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Sop p LL Cs a F = ∑ b ∈ Cs, X (Fin.last K, b) * glAct p LL K a b F := by
  simp only [Sop, Wm, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply]
theorem ring_UU {R : Type} [Ring R] (Wi Wk A Si Sk : R) (h1 : A * Wi = Wi * A - Wi) (h1' : A * Wk = Wk * A - Wk)
    (h2 : A * Si = Si * A - Si) (h2' : A * Sk = Sk * A - Sk) (h3 : Si * Wk = Wk * Si) (h3' : Sk * Wi = Wi * Sk)
    (h4 : Wi * Wk = Wk * Wi) (h5 : Si * Sk - Sk * Si = Wk * Si - Wi * Sk) :
    (Wi * A - Si) * (Wk * A - Sk) = (Wk * A - Sk) * (Wi * A - Si) := by
  have e1 : Wi * A * (Wk * A) = Wi * Wk * A * A - Wi * Wk * A := by
    rw [mul_assoc Wi A, ← mul_assoc A Wk A, h1']; noncomm_ring
  have e1' : Wk * A * (Wi * A) = Wi * Wk * A * A - Wi * Wk * A := by
    rw [mul_assoc Wk A, ← mul_assoc A Wi A, h1, h4]; noncomm_ring
  have e2 : Wi * A * Sk = Wi * Sk * A - Wi * Sk := by
    rw [mul_assoc Wi A, h2']; noncomm_ring
  have e2' : Wk * A * Si = Wk * Si * A - Wk * Si := by
    rw [mul_assoc Wk A, h2]; noncomm_ring
  have e3 : Si * (Wk * A) = Wk * Si * A := by rw [← mul_assoc, h3]
  have e3' : Sk * (Wi * A) = Wi * Sk * A := by rw [← mul_assoc, h3']
  have e5 : Si * Sk = Sk * Si + (Wk * Si - Wi * Sk) := by rw [← h5]; abel
  rw [sub_mul, sub_mul, mul_sub, mul_sub, mul_sub, mul_sub, e1, e1', e2, e2', e3, e3', e5]
  abel
theorem S_S (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (i k : Fin r) (hi : i ∈ Cs) (hk : k ∈ Cs) :
    Sop p LL Cs i * Sop p LL Cs k - Sop p LL Cs k * Sop p LL Cs i =
      (Wm p K k : Module.End ℚ_[p] _) * Sop p LL Cs i - (Wm p K i : Module.End ℚ_[p] _) * Sop p LL Cs k := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Sop_apply, Wm, LinearMap.mulLeft_apply, map_sum, glJ_X_mul]
  rw [Finset.sum_comm (s := Cs) (t := Cs)
    (f := fun b' b => X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F))),
    ← Finset.sum_sub_distrib]
  have e : ∀ b ∈ Cs, (∑ b' ∈ Cs, X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F))) -
      ∑ b' ∈ Cs, X (Fin.last K, b') * (X (Fin.last K, b) * glAct p LL K k b' (glAct p LL K i b F)) =
      (if b = k then X (Fin.last K, k) * ∑ b' ∈ Cs, X (Fin.last K, b') * glAct p LL K i b' F else 0) -
        X (Fin.last K, i) * (X (Fin.last K, b) * glAct p LL K k b F) := by
    intro b _
    rw [← Finset.sum_sub_distrib]
    have e2 : ∀ b' ∈ Cs, X (Fin.last K, b) * (X (Fin.last K, b') * glAct p LL K i b (glAct p LL K k b' F)) -
        X (Fin.last K, b') * (X (Fin.last K, b) * glAct p LL K k b' (glAct p LL K i b F)) =
        (if b = k then X (Fin.last K, k) * (X (Fin.last K, b') * glAct p LL K i b' F) else 0) -
          (if b' = i then X (Fin.last K, i) * (X (Fin.last K, b) * glAct p LL K k b F) else 0) := by
      intro b' _
      have := Formalism.CountingSumsFrames.glAct_comm (p := p) LL K i b k b' F
      rw [sub_eq_iff_eq_add] at this
      rw [this]
      split_ifs with h1 h2 h2
      · subst h1; subst h2; ring
      · subst h1; ring
      · subst h2; ring
      · ring
    rw [Finset.sum_congr rfl e2, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hi]
    congr 1
    split_ifs
    · rw [Finset.mul_sum]
    · simp
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hk, Finset.mul_sum]
theorem Uop_eq_Wm_mul_Aop_sub_Sop (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r) :
    Uop p LL c Cs i = (Wm p K i : Module.End ℚ_[p] _) * Aop p K r c - Sop p LL Cs i := rfl
theorem aop_weightMul_comm (c : ℤ) (i : Fin r) :
    (Aop p K r c : Module.End ℚ_[p] _) * Wm p K i = (Wm p K i : Module.End ℚ_[p] _) * Aop p K r c - Wm p K i := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Aop_apply, Wm, LinearMap.mulLeft_apply, eul_X_mul, mul_sub,
    mul_smul_comm]
  abel
theorem A_S (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i : Fin r) :
    (Aop p K r c : Module.End ℚ_[p] _) * Sop p LL Cs i = Sop p LL Cs i * Aop p K r c - Sop p LL Cs i := by
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Aop_apply, Sop_apply, map_sum, eul_X_mul, eul_glAct, map_sub,
    map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.smul_sum]
  abel
theorem sop_comm_weightMul (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (i k : Fin r) :
    Sop p LL Cs i * Wm p K k = (Wm p K k : Module.End ℚ_[p] _) * Sop p LL Cs i := by
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, Sop_apply, Wm, LinearMap.mulLeft_apply, glJ_X_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring
theorem Wm_mul_Wm_comm (i k : Fin r) :
    (Wm p K i : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) * Wm p K k = Wm p K k * Wm p K i := by
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, Wm, LinearMap.mulLeft_apply]
  ring
theorem U_U (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (i k : Fin r) (hi : i ∈ Cs) (hk : k ∈ Cs)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL c Cs i (Uop p LL c Cs k F) = Uop p LL c Cs k (Uop p LL c Cs i F) := by
  have := ring_UU (Wm p K i : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) (Wm p K k) (Aop p K r c)
    (Sop p LL Cs i) (Sop p LL Cs k) (aop_weightMul_comm c i) (aop_weightMul_comm c k) (A_S LL c Cs i) (A_S LL c Cs k) (sop_comm_weightMul LL Cs i k)
    (sop_comm_weightMul LL Cs k i) (Wm_mul_Wm_comm i k) (S_S LL Cs i k hi hk)
  rw [← Uop_eq_Wm_mul_Aop_sub_Sop, ← Uop_eq_Wm_mul_Aop_sub_Sop] at this
  exact LinearMap.congr_fun this F
end Rel
section GX
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
theorem extendedAction_zero_zero (LL : Letters (K + 1)) (c : ℤ) : EX p (s := s) LL c 0 0 = Aop p K (s + 1) c := rfl
theorem EX_zs (LL : Letters (K + 1)) (c : ℤ) (j : Fin s) :
    EX p (s := s) LL c 0 (Fin.succ j) = dW p K (Fin.castSucc j) := rfl
theorem EX_sz (LL : Letters (K + 1)) (c : ℤ) (i : Fin s) :
    EX p (s := s) LL c (Fin.succ i) 0 = Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i) := rfl
theorem EX_ss (LL : Letters (K + 1)) (c : ℤ) (i j : Fin s) :
    EX p (s := s) LL c (Fin.succ i) (Fin.succ j) = glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j) := rfl
theorem castSucc_mem (i : Fin s) : Fin.castSucc i ∈ (univ : Finset (Fin (s + 1))).erase (Fin.last s) :=
  Finset.mem_erase.mpr ⟨(Fin.castSucc_lt_last i).ne, Finset.mem_univ _⟩
def RelX (p : ℕ) [Fact p.Prime] {K s : ℕ} (LL : Letters (K + 1)) (c0 : ℤ) (a b c d : Fin (s + 1)) : Prop :=
  ∀ x, EX p LL c0 a b (EX p LL c0 c d x) - EX p LL c0 c d (EX p LL c0 a b x) =
    (if b = c then EX p LL c0 a d x else 0) - (if d = a then EX p LL c0 c b x else 0)
theorem RelX.symm {LL : Letters (K + 1)} {c0 : ℤ} {a b c d : Fin (s + 1)} (h : RelX p LL c0 a b c d) :
    RelX p LL c0 c d a b := by
  intro x
  rw [← neg_sub, h x, neg_sub]
theorem relX (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c0 : ℤ) (a b c d : Fin (s + 1)) :
    RelX p LL c0 a b c d := by
  have hAD : ∀ j : Fin s, RelX p LL c0 0 0 0 (Fin.succ j) := by
    intro j x
    rw [if_pos rfl, if_neg (Fin.succ_ne_zero j), extendedAction_zero_zero, EX_zs, A_d, sub_zero]
  have hAU : ∀ i : Fin s, RelX p LL c0 0 0 (Fin.succ i) 0 := by
    intro i x
    rw [if_pos rfl, if_neg (Fin.succ_ne_zero i).symm, extendedAction_zero_zero, EX_sz, A_U, zero_sub]
  have heA : ∀ i j : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) 0 0 := by
    intro i j x
    rw [if_neg (Fin.succ_ne_zero j), if_neg (Fin.succ_ne_zero i).symm, extendedAction_zero_zero, EX_ss, e_A, sub_zero]
  have hDU : ∀ j i : Fin s, RelX p LL c0 0 (Fin.succ j) (Fin.succ i) 0 := by
    intro j i x
    rw [if_pos rfl, extendedAction_zero_zero, EX_zs, EX_sz, EX_ss, d_U LL hv c0 _ _ _ (castSucc_mem j)]
    simp only [Fin.succ_inj, Fin.castSucc_inj]
  have heD : ∀ i j k : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) 0 (Fin.succ k) := by
    intro i j k x
    rw [if_neg (Fin.succ_ne_zero j), EX_zs, EX_zs, EX_ss, dW_apply, dW_apply, dW_apply, pderiv_glAct LL hv]
    simp only [Fin.succ_inj, Fin.castSucc_inj]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  have heU : ∀ i j k : Fin s, RelX p LL c0 (Fin.succ i) (Fin.succ j) (Fin.succ k) 0 := by
    intro i j k x
    rw [if_neg (Fin.succ_ne_zero i).symm, EX_sz, EX_sz, EX_ss,
      raising_comm_holds p K (s + 1) LL c0 _ _ _ _ x hv (castSucc_mem i) (castSucc_mem j), sub_zero]
    simp only [Fin.succ_inj, Fin.castSucc_inj]
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
    refine Fin.cases ?_ (fun k => ?_) c <;> refine Fin.cases ?_ (fun l => ?_) d
  · intro x; simp
  · exact hAD l
  · exact hAU k
  · exact (heA k l).symm
  · exact (hAD j).symm
  · intro x
    rw [if_neg (Fin.succ_ne_zero j), if_neg (Fin.succ_ne_zero l), EX_zs, EX_zs, dW_apply, dW_apply, dW_apply, dW_apply,
      ProjS.pderiv_comm]
    simp
  · exact hDU j k
  · exact (heD k l j).symm
  · exact (hAU i).symm
  · exact (hDU l i).symm
  · intro x
    rw [if_neg (Fin.succ_ne_zero k).symm, if_neg (Fin.succ_ne_zero i).symm, EX_sz, EX_sz,
      U_U LL c0 _ _ _ (castSucc_mem i) (castSucc_mem k)]
    simp
  · exact (heU k l i).symm
  · exact heA i j
  · exact heD i j l
  · exact heU i j k
  · intro x
    rw [EX_ss, EX_ss, EX_ss, EX_ss, Formalism.CountingSumsFrames.glAct_comm]
    simp only [Fin.succ_inj, Fin.castSucc_inj]
theorem coeff_EX_diag (LL : Letters (K + 1)) (c : ℤ) (a : Fin (s + 1))
    (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) :
    coeff m (EX p LL c a a x) = ((wtX LL c m a : ℤ) : ℚ_[p]) * coeff m x := by
  refine Fin.cases ?_ (fun i => ?_) a
  · show coeff m (Aop p K (s + 1) c x) = ((c - ∑ a : Fin (s + 1), (m (Fin.last K, a) : ℤ) : ℤ) : ℚ_[p]) * coeff m x
    rw [Aop_apply, coeff_sub, coeff_smul, ProjS.coeff_eulL, smul_eq_mul]
    push_cast; ring
  · exact coeff_cartan LL (K + 1) _ x m
noncomputable def GX (p : ℕ) [Fact p.Prime] {K s : ℕ} (LL : Letters (K + 1)) (c : ℤ)
    (hv : LL.vec (Fin.last K) = true) : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1) :=
  mkGlW (EX p LL c) (wtX LL c) (fun a b c' d x => relX LL hv c a b c' d x) (coeff_EX_diag LL c)
end GX
end Formalism.InvariantFactorPaths.L4


