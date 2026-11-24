-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:50.500719+00:00
-- url     : https://prove2.me/theorems/394b04e0-6c28-40c9-a81d-03218d5d0747
-- title:
--   Exists Algebra Map Eq Root
-- statement:
--   Definitions and structural lemmas for Exists Algebra Map Eq Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BK_A_le_S
import Theorems.Thm_GlobalTheory_BK_Descent_act_EN
import Theorems.Thm_GlobalTheory_BK_Descent_plus_act_join
import Theorems.Thm_GlobalTheory_BK_E_mul_N_Ezpow
import Theorems.Thm_GlobalTheory_BK_Ezpow_add
import Theorems.Thm_GlobalTheory_BK_Hom_app_EN
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_Mext
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_ext
import Theorems.Thm_GlobalTheory_BK_Hom_app_nabla
import Theorems.Thm_GlobalTheory_BK_Hom_app_phi
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_N_mem
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_mem_Man_of_basis
import Theorems.Thm_GlobalTheory_BK_PhiMod_E_pow_smul_EN
import Theorems.Thm_GlobalTheory_BK_PhiMod_M_le_Man
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mon_eq_zero_iff
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_inl
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_inr
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_phi_extension_generator_eq_zeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul
import Theorems.Thm_GlobalTheory_BK_PhiMod_ext_mono
import Theorems.Thm_GlobalTheory_BK_PhiMod_mem_Mext_invE_of_mem_divE
import Theorems.Thm_GlobalTheory_BK_PhiMod_nabla_mem_MM_of_basis
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_mem_L
import Theorems.Thm_GlobalTheory_BK_PhiMod_plusProj_app
import Theorems.Thm_GlobalTheory_BK_PhiMod_plus_lower
import Theorems.Thm_GlobalTheory_BK_PhiMod_plus_upper
import Theorems.Thm_GlobalTheory_BK_Raises_pow_mem
import Theorems.Thm_GlobalTheory_BK_S_le_R
import Theorems.Thm_GlobalTheory_BK_TameGal_norm_root
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_derivative_mem_R
import Theorems.Thm_GlobalTheory_BK_exists_nabla_rankOne
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_map_Ezpow
import Theorems.Thm_GlobalTheory_BK_mem_divE
import Theorems.Thm_GlobalTheory_BK_mem_ext_rankOne
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_mx_rankOne_eq
import Theorems.Thm_GlobalTheory_BK_phi_bas_rankOne
import Theorems.Thm_GlobalTheory_BK_ringAct_E
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
structure BKDat (η H : ℕ) extends PhiMod O K l e a ι where

  desc : Descent toPhiMod
  nabla_mem : ∀ m ∈ toPhiMod.MM, toPhiMod.nabla m ∈ toPhiMod.MM
  EN_mem : ∀ m ∈ toPhiMod.M, toPhiMod.EN m ∈ toPhiMod.Man
  lower : ∀ m ∈ toPhiMod.M, E K l e ^ H • m ∈ toPhiMod.L
  upper : ∀ m ∈ toPhiMod.L, E K l e ^ η • m ∈ toPhiMod.M
section RankOne
variable {O K l e a}
omit [NeZero a] [TameDescentExponentData K l e a] in
theorem Ezpow_mem_A {i : ℤ} (hi : 0 ≤ i) : Ezpow K l e i ∈ A O K := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [Ezpow_natCast]
  exact pow_mem (E_mem l e _) n
def rankOneDesc (j : ℤ) (χ : TameGal K l e a →* O) :
    Descent (rankOne O K l e fun _ : ZMod a => j) :=
  Descent.ofMatrix _ (fun g _ => Matrix.of fun _ _ => C (algebraMap O K (χ g)))
    (fun g _ _ _ => by
      rw [Matrix.of_apply, ← algebraMap_eq_C]
      exact Subalgebra.algebraMap_mem _ _)
    (fun _ => by ext1 i k; simp [Subsingleton.elim i k])
    (fun g h τ => by
      ext1 i k
      have := congrFun ((ringAct g).commutes (algebraMap O K (χ h))) τ
      simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply, Matrix.map_apply, map_mul]
      exact congrArg _ this.symm)
    fun g τ => by
      ext1 i k
      simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply, Matrix.map_apply,
        mx_rankOne_eq, frob_C]
      rw [map_Ezpow l e _ (congrFun (ringAct_E g) τ), mul_comm]
theorem rankOneDesc_act (j : ℤ) (χ : TameGal K l e a →* O) (g : TameGal K l e a)
    (v : Vec K a Unit) (τ : ZMod a) : (rankOneDesc j χ).act g v τ () =
      C (algebraMap O K (χ g)) * rescale (g.root τ) (v (τ - g.shift) ()) := by
  change Descent.matAct g _ v τ () = _
  simp [Descent.matAct_apply, Matrix.mulVec, dotProduct]
variable [CompleteSpace K]
omit [NeZero a] [TameDescentExponentData K l e a] in
theorem exists_EN_bas_rankOne (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).EN (bas ()) =
      (E K l e * γ - (j : K⟦X⟧) * N K (E K l e)) • bas () := by
  obtain ⟨γ, hγ, h⟩ := exists_nabla_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
  refine ⟨X * γ, mul_mem HasU.X_mem hγ, smul_right_injective _ (r := Ezpow K l e j)
    (Units.ne_zero _) ?_⟩
  have h1 := congrArg (fun v => E K l e • (X : K⟦X⟧) • v) h
  simp only [← PhiMod.conn_apply, PhiMod.conn_smul, smul_add, smul_smul, E_mul_N_Ezpow] at h1
  simp only [PhiMod.EN_apply, smul_smul]
  rw [mul_comm, eq_sub_of_add_eq' h1, ← sub_smul]
  congr 1
  ring
variable (O K l e a) in

def rankOneDat (η H : ℕ) (j : ℤ) (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H) (χ : TameGal K l e a →* O) :
    BKDat O K l e a Unit η H where
  toPhiMod := rankOne O K l e fun _ => j
  desc := rankOneDesc j χ
  nabla_mem _ := by
    have h (i : Unit) := PhiMod.ext_mono _ (A_le_S l e)
      (PhiMod.phi_mem_L _ ((rankOne O K l e fun _ : ZMod a => j).bas_mem_M i))
    refine PhiMod.nabla_mem_MM_of_basis _ (fun i => ?_) h
    obtain ⟨γ, hγ, h'⟩ := exists_nabla_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
    rw [phi_bas_rankOne, h', ← phi_bas_rankOne (O := O)]
    exact Submodule.smul_mem _ (⟨γ, hγ⟩ : S O K e) (h ())
  EN_mem _ hm := PhiMod.EN_mem_Man_of_basis _ (fun i => by
    obtain ⟨γ, hγ, h⟩ := exists_EN_bas_rankOne (O := O) (K := K) (l := l) (e := e) (a := a) j
    rw [h]
    exact PhiMod.smul_mem_Man _ (sub_mem (mul_mem (E_mem l e _) (S_le_R l e hγ))
      (mul_mem (intCast_mem _ j) (N_mem (derivative_mem_R l (E_mem l e _)))))
      (PhiMod.M_le_Man _ (PhiMod.bas_mem_M _ _))) (PhiMod.M_le_Man _ hm)
  lower m hm := (mem_ext_rankOne j).2 fun τ => by
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Ezpow_natCast, ← Ezpow_add]
    exact mul_mem (Ezpow_mem_A (by omega)) (mem_tot.1 hm τ ())
  upper m hm := mem_tot.2 fun τ i => by
    have := mul_mem (Ezpow_mem_A (l := l) (e := e) (i := η + j) (by omega))
      ((mem_ext_rankOne j).1 hm τ)
    rwa [← mul_assoc, ← Ezpow_add, add_neg_cancel_right, Ezpow_natCast] at this
end RankOne
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
abbrev BKHom (D : BKDat O K l e a ι η H) (D' : BKDat O K l e a κ η' H') : Type :=
  Descent.Hom D.desc D'.desc
namespace BKDat
variable (D : BKDat O K l e a ι η H)
abbrev Y : Submodule O (Vec K a ι) := D.desc.Y η
abbrev Y' : Submodule O (Vec K a ι) := D.desc.Y' η
abbrev Yl : Submodule O (Vec K a ι) := D.desc.Yl η
abbrev Minv : Submodule O (Vec K a ι) := D.desc.Minv
abbrev Z : Submodule O D.Pol := D.desc.Z η
abbrev Zl : Submodule K D.Pol := D.desc.Zl η
structure IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) : Prop where
  chars_subset : ∀ τ, D.desc.chars τ ⊆ Sig
  jumps_subset : D.jumps ⊆ U
theorem EN_mem_Man {m : Vec K a ι} (hm : m ∈ D.Man) : D.EN m ∈ D.Man :=
  D.EN_mem_Man_of_basis (fun i => D.EN_mem _ (D.bas_mem_M i)) hm
theorem EN_mem_divE {n : ℕ} {y : Vec K a ι} (hy : y ∈ divE l e n D.Man) :
    D.EN y ∈ divE l e n D.Man := by
  rw [mem_divE, D.E_pow_smul_EN]
  exact sub_mem (D.EN_mem_Man hy) (D.smul_mem_Man
    (mul_mem (natCast_mem _ n) (N_mem (derivative_mem_R l (E_mem l e _)))) hy)
def Lc : Module.End K D.Pol := D.Man.mapQ D.Man D.EN fun _ => D.EN_mem_Man
@[simp] theorem Lc_cls (v : Vec K a ι) : D.Lc (D.cls v) = D.cls (D.EN v) := rfl
theorem Lc_mem_PolEta {n : ℕ} {w : D.Pol} (hw : w ∈ D.PolEta n) : D.Lc w ∈ D.PolEta n := by
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨_, D.EN_mem_divE hy, rfl⟩
theorem actPol_Lc (g : TameGal K l e a) (w : D.Pol) :
    D.desc.actPol g (D.Lc w) = D.Lc (D.desc.actPol g w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Descent.actPol_cls, Descent.actPol_cls, Lc_cls, Descent.act_EN]
theorem Lc_mem_Zl {w : D.Pol} (hw : w ∈ D.Zl) : D.Lc w ∈ D.Zl :=
  ⟨D.Lc_mem_PolEta hw.1, fun g => by rw [actPol_Lc, hw.2 g]⟩
def LcEta : Module.End K (D.PolEta η) := D.Lc.restrict fun _ => D.Lc_mem_PolEta
def LcZ : Module.End K D.Zl := D.Lc.restrict fun _ => D.Lc_mem_Zl
@[simp] theorem coe_LcZ (w : D.Zl) : (D.LcZ w : D.Pol) = D.Lc w := rfl
variable {D} {y : Vec K a ι}
omit [NeZero e] in
theorem mem_invE_of_mem_Y (hy : y ∈ D.Y) : y ∈ D.Mext (invE l e (A O K)) :=
  D.mem_Mext_invE_of_mem_divE hy.1
abbrev plusMod (hy : y ∈ D.Y) : PhiMod O K l e a (ι ⊕ Unit) := D.plus (mem_invE_of_mem_Y hy)
abbrev plusDesc (hy : y ∈ D.Y) : Descent (plusMod hy) := D.desc.plus (mem_invE_of_mem_Y hy) hy.2
omit [NeZero e] in

theorem plusMod_upper (hy : y ∈ D.Y) : ∀ v ∈ (plusMod hy).L, E K l e ^ η • v ∈ (plusMod hy).M :=
  D.plus_upper _ D.upper hy.1
def plusDat (hy : y ∈ D.Y) (hMon : D.Mon y = 0) (hz : ∃ w ∈ D.MM, D.zeta y = (X : K⟦X⟧) • w)
    (hH : E K l e ^ H • y ∈ D.L) : BKDat O K l e a (ι ⊕ Unit) η H where
  toPhiMod := plusMod hy
  desc := plusDesc hy
  nabla_mem _ := PhiMod.nabla_mem_MM_of_basis _ (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [D.bas_inl (mem_invE_of_mem_Y hy), ← Hom.app_phi, ← Hom.app_nabla]
      exact Hom.app_mem_ext _ (A_le_S l e) (D.nabla_mem _
        (D.ext_mono (A_le_S l e) (D.phi_mem_L (D.bas_mem_M i))))
    · obtain ⟨w, hw, h⟩ := hz
      have h1 := D.conn_phi_extension_generator_eq_zeta (mem_invE_of_mem_Y hy)
      rw [h, map_smul, PhiMod.conn_apply] at h1
      rw [PhiMod.bas_inr, smul_right_injective _ X_ne_zero h1]
      exact Hom.app_mem_ext _ (A_le_S l e) hw)
    fun i => PhiMod.ext_mono _ (A_le_S l e) (PhiMod.phi_mem_L _ (PhiMod.bas_mem_M _ i))
  EN_mem _ hm := PhiMod.EN_mem_Man_of_basis _ (by
    rintro (i | ⟨⟨⟩⟩)
    · rw [D.bas_inl (mem_invE_of_mem_Y hy), ← Hom.app_EN]
      exact Hom.app_mem_Mext _ (A_le_Rpi l e) (D.EN_mem _ (D.bas_mem_M i))
    · rw [PhiMod.bas_inr]
      exact (D.Mon_eq_zero_iff _).1 hMon) (PhiMod.M_le_Man _ hm)
  lower := D.plus_lower _ D.lower hH
  upper := plusMod_upper hy
end BKDat
namespace Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
def avg : Module.End K (Vec K a ι) :=
  letI := Fintype.ofFinite (TameGal K l e a)
  ((Nat.card (TameGal K l e a) : K)⁻¹) • ∑ g, Δ.act g
end Descent
section Examples
omit [NeZero a] [TameDescentExponentData K l e a]
end Examples
section Examples
variable [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H)
def splitDat (χ : TameGal K l e a →* O) : BKDat O K l e a (Unit ⊕ Unit) η H :=
  BKDat.plusDat (D := rankOneDat O K l e a η H j h₁ h₂ χ) (y := 0) (zero_mem _) (map_zero _)
    ⟨0, zero_mem _, by simp⟩ (by simp)
example (χ : TameGal K l e a →* O) :
    BKHom (rankOneDat O K l e a η H j h₁ h₂ χ) (splitDat h₁ h₂ χ) :=
  Descent.plusInl _ _ (zero_mem _)
end Examples
example : BKDat ℤ_[3] ℚ_[3] 3 2 1 Unit 1 2 := rankOneDat _ _ _ _ _ 1 2 (-1) (by simp) (by simp) 1
def Descent.plusProj {P : PhiMod O K l e a ι} (Δ : Descent P) {y : Vec K a ι}
    (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv) :
    Descent.Hom (Δ.plus hy hinv) (rankOneDesc 0 1) where
  toHom := P.plusProj hy
  app_act g w := by
    rw [← join_eta w, Descent.plus_act_join, P.plusProj_app, P.plusProj_app]
    ext τ i : 2
    refine Eq.trans ?_ (rankOneDesc_act 0 1 g _ τ).symm
    simp [ringAct_apply]
section Omega
omit [NeZero a] [TameDescentExponentData K l e a]
variable [TameDescentExponentData K l e 1]
omit [IsUltrametricDist K] in
theorem exists_algebraMap_eq_root (g : TameGal K l e 1) : ∃ c : O, algebraMap O K c = g.root 0 :=
  (IsUnitBall.mem_range_iff (O := O) (g.root 0)).2 (g.norm_root 0).le
variable (O) in

def omegaOne : TameGal K l e 1 →* O where
  toFun g := (exists_algebraMap_eq_root g).choose
  map_one' := IsUnitBall.inj (K := K) (by
    rw [(exists_algebraMap_eq_root _).choose_spec, TameGal.root_one, map_one])
  map_mul' g h := IsUnitBall.inj (K := K) (by
    rw [map_mul, (exists_algebraMap_eq_root _).choose_spec, (exists_algebraMap_eq_root _).choose_spec,
      (exists_algebraMap_eq_root _).choose_spec, TameGal.root_mul, Subsingleton.elim (0 - g.shift) 0])
end Omega
end GlobalTheory.BK


