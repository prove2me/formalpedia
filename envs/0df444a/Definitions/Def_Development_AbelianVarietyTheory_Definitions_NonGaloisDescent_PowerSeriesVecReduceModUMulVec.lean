-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:14:35.442148+00:00
-- url     : https://prove2.me/theorems/ddfe03d7-efc4-4b51-af04-10bbd5d3a149
-- title:
--   Power Series Vec Reduce Mod UMul Vec
-- statement:
--   Definitions and structural lemmas for Power Series Vec Reduce Mod UMul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Theorems.Thm_GlobalTheory_BK_norm_factorial_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology Matrix
abbrev Vec (K : Type) (a : ℕ) (ι : Type) : Type := ZMod a → ι → K⟦X⟧
section Vecs
variable {O K : Type} [CommRing O] [NormedField K] [Algebra O K] {a : ℕ} {ι : Type}
variable (ι) in

def vecs (B : Subalgebra O K⟦X⟧) : Submodule B (ι → K⟦X⟧) where
  carrier := {v | ∀ i, v i ∈ B}
  add_mem' hv hw i := B.add_mem (hv i) (hw i)
  zero_mem' _ := B.zero_mem
  smul_mem' c _ hv i := B.mul_mem c.2 (hv i)
def tot {B : Subalgebra O K⟦X⟧} (P : ZMod a → Submodule B (ι → K⟦X⟧)) :
    Submodule B (Vec K a ι) := Submodule.pi Set.univ P
def red0 : (ι → K⟦X⟧) →ₗ[K] (ι → K) where
  toFun v i := constantCoeff (v i)
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
@[simp] theorem powerSeriesVecReduceModU_apply (v : ι → K⟦X⟧) (i : ι) : red0 v i = constantCoeff (v i) := rfl
def red : Vec K a ι →ₗ[K] (ZMod a → ι → K) where
  toFun v τ := red0 (v τ)
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
@[simp] theorem red_apply (v : Vec K a ι) (τ : ZMod a) : red v τ = red0 (v τ) := rfl
def frobV (l : ℕ) [Fact l.Prime] : (ι → K⟦X⟧) →ₗ[K] (ι → K⟦X⟧) where
  toFun v i := frob K l (v i)
  map_add' v w := by ext1; simp
  map_smul' c v := by ext1; simp
@[simp] theorem frobV_apply (l : ℕ) [Fact l.Prime] (v : ι → K⟦X⟧) (i : ι) :
    frobV l v i = frob K l (v i) := rfl
variable (K a) in

def frobTot (l : ℕ) [Fact l.Prime] : (ZMod a → K⟦X⟧) →ₐ[K] (ZMod a → K⟦X⟧) :=
  AlgHom.pi fun τ => (frob K l).comp (Pi.evalAlgHom K (fun _ : ZMod a => K⟦X⟧) (τ - 1))
@[simp] theorem frobTot_apply (l : ℕ) [Fact l.Prime] (f : ZMod a → K⟦X⟧) (τ : ZMod a) :
    frobTot K a l f τ = frob K l (f (τ - 1)) := rfl
theorem powerSeriesVecReduceModU_mulVec {κ : Type} [Fintype ι] (Y : Matrix κ ι K⟦X⟧) (v : ι → K⟦X⟧) :
    red0 (Y *ᵥ v) = Y.map constantCoeff *ᵥ red0 v := by
  ext i
  exact RingHom.map_mulVec constantCoeff Y v i
end Vecs
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
structure PhiMod where

  mat : ZMod a → GL ι (invE l e (A O K))
abbrev Mc : Submodule (A O K) (ι → K⟦X⟧) := vecs ι (A O K)
namespace PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)
def mx (τ : ZMod a) : Matrix ι ι K⟦X⟧ :=
  (P.mat τ : Matrix ι ι (invE l e (A O K))).map (invE l e (A O K)).val
def mxInv (τ : ZMod a) : Matrix ι ι K⟦X⟧ :=
  (((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) : Matrix ι ι (invE l e (A O K))).map
    (invE l e (A O K)).val
theorem mx_mul_mxInv (τ : ZMod a) : P.mx τ * P.mxInv τ = 1 := by
  rw [mx, mxInv, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem mxInv_mul_mx (τ : ZMod a) : P.mxInv τ * P.mx τ = 1 := by
  rw [mx, mxInv, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)
def ofMatrix (Y Y' : ZMod a → Matrix ι ι K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K))
    (hY' : ∀ τ i j, Y' τ i j ∈ invE l e (A O K)) (h : ∀ τ, Y τ * Y' τ = 1) :
    PhiMod O K l e a ι where
  mat τ :=
    { val := Matrix.of fun i j => ⟨Y τ i j, hY τ i j⟩
      inv := Matrix.of fun i j => ⟨Y' τ i j, hY' τ i j⟩
      val_inv := Matrix.map_injective (f := (invE l e (A O K)).val) Subtype.val_injective (by
        dsimp only
        rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact h τ)
      inv_val := Matrix.map_injective (f := (invE l e (A O K)).val) Subtype.val_injective (by
        dsimp only
        rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact mul_eq_one_comm.1 (h τ)) }
@[simp] theorem mx_ofMatrix (Y Y' : ZMod a → Matrix ι ι K⟦X⟧)
    (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) (hY' : ∀ τ i j, Y' τ i j ∈ invE l e (A O K))
    (h : ∀ τ, Y τ * Y' τ = 1) (τ : ZMod a) : (ofMatrix Y Y' hY hY' h).mx τ = Y τ := rfl
def M (_ : PhiMod O K l e a ι) : Submodule (A O K) (Vec K a ι) := tot fun _ => Mc O K ι
def Mext (_ : PhiMod O K l e a ι) (B : Subalgebra O K⟦X⟧) : Submodule B (Vec K a ι) :=
  tot fun _ => vecs ι B
def extc (B : Subalgebra O K⟦X⟧) (τ : ZMod a) : Submodule B (ι → K⟦X⟧) :=
  Submodule.span B (Set.range (P.mx τ).col)
def ext (B : Subalgebra O K⟦X⟧) : Submodule B (Vec K a ι) := tot (P.extc B)
abbrev Lcomp (τ : ZMod a) : Submodule (A O K) (ι → K⟦X⟧) := P.extc (A O K) τ
abbrev L : Submodule (A O K) (Vec K a ι) := P.ext (A O K)
abbrev MM : Submodule (S O K e) (Vec K a ι) := P.ext (S O K e)
abbrev MMl : Submodule (invL l (S O K e)) (Vec K a ι) := P.ext (invL l (S O K e))
abbrev Lk (k : ℝ) : Submodule (R O K l k) (Vec K a ι) := P.ext (R O K l k)
def FilMM (j : ℕ) : Submodule (S O K e) (Vec K a ι) := Fil O K l e j • P.MM
theorem mem_extc {B : Subalgebra O K⟦X⟧} {τ : ZMod a} {v : ι → K⟦X⟧} :
    v ∈ P.extc B τ ↔ ∃ m ∈ vecs ι B, v = P.mx τ *ᵥ m := by
  rw [extc, Submodule.mem_span_range_iff_exists_fun]
  have key (c : ι → B) : ∑ i, c i • (P.mx τ).col i = P.mx τ *ᵥ fun i => (c i : K⟦X⟧) := by
    ext1 j
    simp [Matrix.mulVec, dotProduct, Subalgebra.smul_def, mul_comm]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, fun i => (c i).2, key c⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨fun i => ⟨m i, hm i⟩, key _⟩
theorem mem_extc_iff {B : Subalgebra O K⟦X⟧} {τ : ZMod a} {v : ι → K⟦X⟧} :
    v ∈ P.extc B τ ↔ P.mxInv τ *ᵥ v ∈ vecs ι B := by
  rw [mem_extc]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rwa [Matrix.mulVec_mulVec, mxInv_mul_mx, Matrix.one_mulVec]
  · intro h
    exact ⟨_, h, by rw [Matrix.mulVec_mulVec, mx_mul_mxInv, Matrix.one_mulVec]⟩
theorem linearIndependent_col (B : Subalgebra O K⟦X⟧) (τ : ZMod a) :
    LinearIndependent B (P.mx τ).col := by
  have h : LinearIndependent K⟦X⟧ (P.mx τ).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero
      (Matrix.isUnit_det_of_right_inverse (P.mx_mul_mxInv τ)).ne_zero
  exact h.restrict_scalars' B
def basisExt (B : Subalgebra O K⟦X⟧) (τ : ZMod a) : Module.Basis ι B (P.extc B τ) :=
  Module.Basis.span (P.linearIndependent_col B τ)
@[simp] theorem coe_basisExt (B : Subalgebra O K⟦X⟧) (τ : ZMod a) (i : ι) :
    (P.basisExt B τ i : ι → K⟦X⟧) = (P.mx τ).col i :=
  congrArg Subtype.val (Module.Basis.span_apply _ i)
abbrev D (_ : PhiMod O K l e a ι) : Type := ZMod a → ι → K
def uL (τ : ZMod a) : Submodule (A O K) (P.Lcomp τ) := Ideal.span {uIn (A O K)} • ⊤
theorem mem_uL_iff {τ : ZMod a} {v : P.Lcomp τ} : v ∈ P.uL τ ↔ red0 (v : ι → K⟦X⟧) = 0 := by
  rw [uL, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, -, rfl⟩
    ext i
    simp [Subalgebra.smul_def]
  · intro h
    have hm := P.mem_extc_iff.1 v.2
    have h0 : red0 (P.mxInv τ *ᵥ v) = 0 := by rw [powerSeriesVecReduceModU_mulVec, h, Matrix.mulVec_zero]
    have h1 (i : ι) : X * PowerSeries.mk (fun n => coeff (n + 1) ((P.mxInv τ *ᵥ v) i)) =
        (P.mxInv τ *ᵥ v) i := by
      have := PowerSeries.eq_X_mul_shift_add_const ((P.mxInv τ *ᵥ v) i)
      rw [show constantCoeff ((P.mxInv τ *ᵥ v) i) = 0 from congrFun h0 i, map_zero,
        add_zero] at this
      exact this.symm
    refine ⟨⟨P.mx τ *ᵥ fun i => PowerSeries.mk fun n => coeff (n + 1) ((P.mxInv τ *ᵥ v) i),
      P.mem_extc.2 ⟨_, fun i n => by rw [coeff_mk]; exact hm i _, rfl⟩⟩, trivial, Subtype.ext ?_⟩
    change (X : K⟦X⟧) • (P.mx τ *ᵥ _) = _
    rw [← Matrix.mulVec_smul]
    have : ((X : K⟦X⟧) • fun i => PowerSeries.mk fun n => coeff (n + 1) ((P.mxInv τ *ᵥ v) i)) =
        P.mxInv τ *ᵥ v := funext h1
    rw [this, Matrix.mulVec_mulVec, mx_mul_mxInv, Matrix.one_mulVec]
def redQ (τ : ZMod a) : (P.Lcomp τ ⧸ (P.uL τ).restrictScalars O) →ₗ[O] (ι → K) :=
  Submodule.liftQ _ ((red0.restrictScalars O).comp ((P.Lcomp τ).subtype.restrictScalars O))
    fun _ hv => P.mem_uL_iff.1 hv
def mx0 (τ : ZMod a) : Matrix ι ι K := (P.mx τ).map constantCoeff
theorem matrix_mul_inv_const_eq_one (τ : ZMod a) : P.mx0 τ * (P.mxInv τ).map constantCoeff = 1 := by
  rw [mx0, ← Matrix.map_mul, mx_mul_mxInv, Matrix.map_one _ (map_zero _) (map_one _)]
theorem inv_const_mul_matrix_eq_one (τ : ZMod a) : (P.mxInv τ).map constantCoeff * P.mx0 τ = 1 :=
  mul_eq_one_comm.1 (P.matrix_mul_inv_const_eq_one τ)
def phiD : P.D ≃ₗ[K] P.D where
  toFun d τ := P.mx0 τ *ᵥ d (τ - 1)
  map_add' d d' := by ext1; simp [Matrix.mulVec_add]
  map_smul' c d := by ext1; simp [Matrix.mulVec_smul]
  invFun d τ := (P.mxInv (τ + 1)).map constantCoeff *ᵥ d (τ + 1)
  left_inv d := by ext1; simp [inv_const_mul_matrix_eq_one]
  right_inv d := by ext1; simp [matrix_mul_inv_const_eq_one]
variable [Fact l.Prime]
def phi : Vec K a ι →ₗ[K] Vec K a ι where
  toFun v τ := P.mx τ *ᵥ frobV l (v (τ - 1))
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]
variable [NormedAlgebra ℚ_[l] K]
end PhiMod
section Hom
variable {O K l e a ι} [Fact l.Prime] {κ μ : Type} [Fintype κ] [DecidableEq κ] [Fintype μ]
  [DecidableEq μ]
structure Hom (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) where

  mat : ZMod a → Matrix κ ι K⟦X⟧
  mem : ∀ τ i j, mat τ i j ∈ A O K
  comm : ∀ τ, mat τ * P.mx τ = Q.mx τ * (mat (τ - 1)).map (frob K l)
namespace Hom
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
def app (F : Hom P Q) : Vec K a ι →ₗ[K⟦X⟧] Vec K a κ where
  toFun v τ := F.mat τ *ᵥ v τ
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]
def onD (F : Hom P Q) : P.D →ₗ[K] Q.D where
  toFun d τ := (F.mat τ).map constantCoeff *ᵥ d τ
  map_add' v w := by ext1; simp [Matrix.mulVec_add]
  map_smul' c v := by ext1; simp [Matrix.mulVec_smul]
variable (P) in

def scalar (c : O) : Hom P P where
  mat _ := algebraMap O K⟦X⟧ c • (1 : Matrix ι ι K⟦X⟧)
  mem τ i j := by
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · simp
    · simp
  comm τ := by
    have : (algebraMap O K⟦X⟧ c • (1 : Matrix ι ι K⟦X⟧)).map (frob K l) =
        algebraMap O K⟦X⟧ c • (1 : Matrix ι ι K⟦X⟧) := by
      ext1 i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, algebraMap_eq_C]
      split_ifs <;> simp
    rw [this]
    simp
def comp (G : Hom Q T) (F : Hom P Q) : Hom P T where
  mat τ := G.mat τ * F.mat τ
  mem τ i j := Subalgebra.sum_mem _ fun k _ => mul_mem (G.mem τ i k) (F.mem τ k j)
  comm τ := by
    rw [Matrix.mul_assoc, F.comm, ← Matrix.mul_assoc, G.comm, Matrix.mul_assoc, Matrix.map_mul]
end Hom
end Hom
section Hat
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable {K} in
open Classical in

def hat (f : K⟦X⟧) : AhatE O K l e :=
  if h : f ∈ RpiE O K l e then toHatE O K l e ⟨f, h⟩ else 0
variable {O K}
variable {ι}
variable (O) in

def hatV (v : ι → K⟦X⟧) : ι → AhatE O K l e := fun i => hat O l e (v i)
variable (O) in

def hatSpan (N : Set (ι → K⟦X⟧)) : Submodule (Ahat O K l e) (ι → AhatE O K l e) :=
  Submodule.span _ (hatV O l e '' (N ∩ vecs ι (RpiE O K l e)))
variable (O K ι) in

def Mhatc : Submodule (Ahat O K l e) (ι → AhatE O K l e) := hatSpan O l e (Mc O K ι)
namespace PhiMod
variable {l e a} (P : PhiMod O K l e a ι)
def Mhat (_ : PhiMod O K l e a ι) : Submodule (Ahat O K l e) (ZMod a → ι → AhatE O K l e) :=
  Submodule.pi Set.univ fun _ => Mhatc O K l e ι
def Lhatc (τ : ZMod a) : Submodule (Ahat O K l e) (ι → AhatE O K l e) :=
  hatSpan O l e (P.Lcomp τ)
def Lhat : Submodule (Ahat O K l e) (ZMod a → ι → AhatE O K l e) := Submodule.pi Set.univ P.Lhatc
def hatTot (_ : PhiMod O K l e a ι) (v : Vec K a ι) : ZMod a → ι → AhatE O K l e :=
  fun τ => hatV O l e (v τ)
end PhiMod
end Hat
section RankOne
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
def Eunit : (invE l e (A O K))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := invE l e (A O K)) (EIn l e (A O K))).unit
variable {a} in

def rankOne (j : ZMod a → ℤ) : PhiMod O K l e a Unit where
  mat τ := Units.map (Matrix.scalar Unit).toMonoidHom (Eunit O K l e ^ j τ)
variable {O K l e a}
end RankOne
example [Fact (Nat.Prime 3)] : PhiMod ℤ_[3] ℚ_[3] 3 8 2 Unit := rankOne _ _ _ _ fun _ => 5
example [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] :
    monomial (e * l) ((l.factorial : K)⁻¹) ∈ S O K e ∧
      monomial (e * l) ((l.factorial : K)⁻¹) ∉ A O K := by
  have h0 : ‖(l.factorial : K)‖ ≠ 0 := norm_ne_zero_iff.2 (natCast_ne_zero' l l.factorial_ne_zero)
  refine ⟨monomial_mem_S ?_, fun h => ?_⟩
  · rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_inv, inv_mul_cancel₀ h0]
  · have h1 := h (e * l)
    rw [coeff_monomial_same, norm_inv] at h1
    have h2 := norm_factorial_le (K := K) l l
    rw [Nat.div_self (Fact.out : l.Prime).pos, pow_one] at h2
    have h3 := h2.trans_lt (norm_l_lt_one l)
    exact absurd ((inv_le_one₀ (lt_of_le_of_ne (norm_nonneg _) h0.symm)).1 h1) (not_le.2 h3)
end GlobalTheory.BK


