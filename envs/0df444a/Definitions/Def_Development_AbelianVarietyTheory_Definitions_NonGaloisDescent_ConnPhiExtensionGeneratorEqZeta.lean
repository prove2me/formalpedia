-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:25:34.709595+00:00
-- url     : https://prove2.me/theorems/d5fcfc3c-eb75-4814-ae3e-2800baa246a2
-- title:
--   Conn Phi Extension Generator Eq Zeta
-- statement:
--   Definitions and structural lemmas for Conn Phi Extension Generator Eq Zeta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_PhiMod_mxInv_mem
import Theorems.Thm_GlobalTheory_BK_PhiMod_mx_mem
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_mx_rankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology Matrix
section Lim
variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}
def ulim (s : ℕ → K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff n (s n)
theorem ulim_sub_dvd {s : ℕ → K⟦X⟧} (h : ∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ s (n + 1) - s n) (n : ℕ) :
    (X : K⟦X⟧) ^ (n + 1) ∣ ulim s - s n := by
  have key (m k : ℕ) : (X : K⟦X⟧) ^ (m + 1) ∣ s (m + k) - s m := by
    induction k with
    | zero => simp
    | succ k ih =>
      have := dvd_add ((pow_dvd_pow _ (by omega : m + 1 ≤ m + k + 1)).trans (h (m + k))) ih
      rwa [sub_add_sub_cancel] at this
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 hm)
  have := X_pow_dvd_iff.1 (key m k) m (Nat.lt_succ_self m)
  rw [map_sub] at this ⊢
  rw [ulim, coeff_mk, ← neg_sub, this, neg_zero]
variable (K a ι) in

def uPow (m : ℕ) : Submodule K⟦X⟧ (Vec K a ι) where
  carrier := {v | ∀ τ i, (X : K⟦X⟧) ^ m ∣ v τ i}
  add_mem' hv hw τ i := dvd_add (hv τ i) (hw τ i)
  zero_mem' _ _ := dvd_zero _
  smul_mem' c _ hv τ i := (hv τ i).mul_left c
theorem X_pow_dvd_frob (l : ℕ) [Fact l.Prime] {m : ℕ} {f : K⟦X⟧} (h : (X : K⟦X⟧) ^ (m + 1) ∣ f) :
    (X : K⟦X⟧) ^ (m + 2) ∣ frob K l f := by
  have h1 := map_dvd (frob K l) h
  rw [map_pow, frob_X, ← pow_mul] at h1
  have := (Fact.out : l.Prime).two_le
  exact (pow_dvd_pow _ (by nlinarith)).trans h1
def geom (T : Module.End K (Vec K a ι)) : Module.End K (Vec K a ι) where
  toFun w τ i := ulim fun n => (∑ j ∈ Finset.range (n + 1), T ^ j) w τ i
  map_add' v w := by ext τ i n; simp [ulim, Finset.sum_add_distrib]
  map_smul' c w := by ext τ i n; simp [ulim, Finset.mul_sum]
def Raises (T : Module.End K (Vec K a ι)) : Prop :=
  ∀ m, ∀ v ∈ uPow K a ι (m + 1), T v ∈ uPow K a ι (m + 2)
def cst : (ZMod a → ι → K) →ₗ[K] Vec K a ι where
  toFun d τ i := C (d τ i)
  map_add' d d' := by ext τ i : 2; simp
  map_smul' c d := by ext τ i : 2; simp [smul_eq_C_mul]
@[simp] theorem cst_apply (d : ZMod a → ι → K) (τ : ZMod a) (i : ι) : cst d τ i = C (d τ i) := rfl
@[simp] theorem red_cst (d : ZMod a → ι → K) : red (cst d) = d := by ext τ i; simp
def derV : Module.End K (Vec K a ι) where
  toFun v τ i := PowerSeries.derivative K (v τ i)
  map_add' v w := by ext τ i : 2; simp
  map_smul' c v := by ext τ i : 2; simp
@[simp] theorem derV_apply (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    derV v τ i = PowerSeries.derivative K (v τ i) := rfl
def derTot (f : ZMod a → K⟦X⟧) : ZMod a → K⟦X⟧ := fun τ => PowerSeries.derivative K (f τ)
def NTot (f : ZMod a → K⟦X⟧) : ZMod a → K⟦X⟧ := fun τ => N K (f τ)
def bas [DecidableEq ι] (i : ι) : Vec K a ι := fun _ => Pi.single i 1
end Lim
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
namespace PhiMod
variable (P : PhiMod O K l e a ι)
def xiSeq (n : ℕ) : ZMod a → Matrix ι ι K⟦X⟧ :=
  (fun Y τ => P.mx τ * (Y (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C)^[n]
    fun _ => 1
theorem xiSeq_zero (τ : ZMod a) : P.xiSeq 0 τ = 1 := rfl
theorem xiSeq_succ (n : ℕ) (τ : ZMod a) : P.xiSeq (n + 1) τ =
    P.mx τ * (P.xiSeq n (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C := by
  rw [xiSeq, Function.iterate_succ_apply']
  rfl
theorem xiSeq_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 1) ∣ P.xiSeq (n + 1) τ i j - P.xiSeq n τ i j := by
  induction n generalizing τ i j with
  | zero =>
    have h := congrFun (congrFun (P.matrix_mul_inv_const_eq_one τ) i) j
    rw [zero_add, pow_one, X_dvd_iff]
    simp only [xiSeq_succ, xiSeq_zero, Matrix.map_one _ (map_zero (frob K l)) (map_one _), Matrix.mul_one, map_sub]
    rw [Matrix.mul_apply] at h ⊢
    simp only [map_sum, map_mul, Matrix.map_apply, constantCoeff_C, mx0] at h ⊢
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [← Matrix.sub_apply, xiSeq_succ P (n + 1), xiSeq_succ P n τ, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
    rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun m _ => Dvd.dvd.mul_left ?_ _
    rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub]
    exact X_pow_dvd_frob l (ih (τ - 1) m k)
def xiMat (τ : ZMod a) : Matrix ι ι K⟦X⟧ := Matrix.of fun i j => ulim fun n => P.xiSeq n τ i j
theorem xiMat_sub_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 1) ∣ P.xiMat τ i j - P.xiSeq n τ i j :=
  ulim_sub_dvd (s := fun n => P.xiSeq n τ i j) (fun n => P.xiSeq_dvd n τ i j) n
theorem xiMat_map_constantCoeff (τ : ZMod a) : (P.xiMat τ).map constantCoeff = 1 := by
  ext i j
  have := P.xiMat_sub_dvd 0 τ i j
  rw [zero_add, pow_one, X_dvd_iff, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, xiSeq_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
theorem isUnit_det_xiMat (τ : ZMod a) : IsUnit (P.xiMat τ).det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, xiMat_map_constantCoeff]
  simp
def xiExt : Vec K a ι ≃ₗ[K] Vec K a ι where
  toFun w τ := P.xiMat τ *ᵥ w τ
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]
  invFun v τ := (P.xiMat τ)⁻¹ *ᵥ v τ
  left_inv w := by ext1 τ; simp [Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ)]
  right_inv w := by ext1 τ; simp [Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)]
theorem xiExt_apply (w : Vec K a ι) (τ : ZMod a) : P.xiExt w τ = P.xiMat τ *ᵥ w τ := rfl
def xi : P.D →ₗ[K] Vec K a ι := P.xiExt.toLinearMap ∘ₗ cst
theorem xi_apply (d : P.D) : P.xi d = P.xiExt (cst d) := rfl
theorem red_xiExt (w : Vec K a ι) : red (P.xiExt w) = red w := by
  ext1 τ
  rw [red_apply, xiExt_apply, powerSeriesVecReduceModU_mulVec, xiMat_map_constantCoeff, Matrix.one_mulVec, red_apply]
@[simp] theorem red_xi (d : P.D) : red (P.xi d) = d := by rw [xi_apply, red_xiExt, red_cst]
def nabla : Module.End K (Vec K a ι) := P.xiExt.conj derV
def conn : Module.End K (Vec K a ι) where
  toFun v := (X : K⟦X⟧) • P.nabla v
  map_add' v w := by rw [map_add, smul_add]
  map_smul' c v := by rw [map_smul, smul_comm]; rfl
theorem conn_apply (v : Vec K a ι) : P.conn v = (X : K⟦X⟧) • P.nabla v := rfl
theorem nabla_xiExt (w : Vec K a ι) : P.nabla (P.xiExt w) = P.xiExt (derV w) := by
  simp [nabla, LinearEquiv.conj_apply]
@[simp] theorem nabla_xi (d : P.D) : P.nabla (P.xi d) = 0 := by
  rw [xi_apply, nabla_xiExt, ← map_zero P.xiExt]
  congr 1
  ext τ i : 2
  simp
@[simp] theorem conn_xi (d : P.D) : P.conn (P.xi d) = 0 := by rw [conn_apply, nabla_xi, smul_zero]
end PhiMod
namespace PhiMod
variable (P : PhiMod O K l e a ι)
def lphi : Module.End K (Vec K a ι) := (l : K) • P.phi
def zeta : Module.End K (Vec K a ι) := -(geom P.lphi * P.lphi * P.conn)
end PhiMod
namespace Hom
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
end Hom
section Plus
def join (v : Vec K a ι) (f : ZMod a → K⟦X⟧) : Vec K a (ι ⊕ Unit) :=
  fun τ => Sum.elim (v τ) fun _ => f τ
def xVec : Vec K a (ι ⊕ Unit) := join 0 1
namespace PhiMod
variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
omit [Fact l.Prime] in

def plus : PhiMod O K l e a (ι ⊕ Unit) :=
  ofMatrix (fun τ => Matrix.fromBlocks (P.mx τ) (Matrix.replicateCol Unit (y τ)) 0 1)
    (fun τ => Matrix.fromBlocks (P.mxInv τ) (Matrix.replicateCol Unit (-(P.mxInv τ *ᵥ y τ))) 0 1)
    (by
      rintro τ (i | i) (j | j)
      exacts [P.mx_mem τ i j, mem_tot.1 hy τ i, zero_mem _, one_mem _])
    (by
      rintro τ (i | i) (j | j)
      exacts [P.mxInv_mem τ i j, neg_mem (Subalgebra.sum_mem _ fun k _ =>
        mul_mem (P.mxInv_mem τ i k) (mem_tot.1 hy τ k)), zero_mem _, one_mem _])
    fun τ => by
      rw [Matrix.fromBlocks_multiply, ← Matrix.replicateCol_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, mx_mul_mxInv]
      simp [← Matrix.replicateCol_add]
def plusInl : Hom P (P.plus hy) where
  mat _ := Matrix.fromRows 1 0
  mem := by
    rintro τ (i | i) j
    · rw [Matrix.fromRows_apply_inl, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · exact zero_mem _
  comm τ := by
    rw [plus, mx_ofMatrix, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    simp
variable [NormedAlgebra ℚ_[l] K] [NeZero e]
def plusProj : Hom (P.plus hy) (rankOne O K l e fun _ => 0) where
  mat _ := Matrix.fromCols 0 1
  mem := by
    rintro τ i (j | j)
    exacts [zero_mem _, one_mem _]
  comm τ := by
    have h : (rankOne O K l e fun _ : ZMod a => 0).mx τ = 1 := by
      ext1 i j
      exact (mx_rankOne (n := 0) rfl).trans (pow_zero _)
    rw [h, plus, mx_ofMatrix, Matrix.fromCols_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_zero _ (map_zero _), Matrix.fromCols_mul_fromBlocks]
    simp
end PhiMod
end Plus
end GlobalTheory.BK


