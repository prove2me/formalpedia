-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:05.461138+00:00
-- url     : https://prove2.me/theorems/777c2705-834f-47da-830f-f02b03532e33
-- title:
--   DUnit Mem Range Of Mem Ker Ideal
-- statement:
--   Definitions and structural lemmas for DUnit Mem Range Of Mem Ker Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DUnitMemRangeOfMemKerIdeal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_exact_kerMap_map
import Theorems.Thm_GlobalTheory_AugCot_map_surjective
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_cotMap_pow
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_le_ker_iff
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT


set_option autoImplicit false
noncomputable section
open Coalgebra Bialgebra WithConv
namespace GlobalTheory
namespace PDiv
variable {R A C D : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing D]
  [Bialgebra R A] [Bialgebra R C] [Bialgebra R D]
theorem cotMap_surjective {f : C →ₐc[R] A} (hf : Function.Surjective f) :
    Function.Surjective (cotMap f) :=
  AugCot.map_surjective _ _ hf
theorem dUnit_mem_range_of_mem_kerIdeal (g : D →ₐc[R] C) {c : C} (hc : c ∈ kerIdeal g) :
    dUnit R c ∈ LinearMap.range (cotMap g) := by
  suffices h : counitAlgHom R C c = 0 ∧ dUnit R c ∈ LinearMap.range (cotMap g) from h.2
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, dUnit R a, cotMap_d g a⟩
    have ha' : counit (R := R) a = 0 := ha
    simpa using ha'
  | zero => exact ⟨map_zero _, by rw [dUnit, map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [map_add, hx.1, hy.1, add_zero], by rw [dUnit, map_add]; exact add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero], ?_⟩
    rw [smul_eq_mul, dUnit, AugCot.d_mul, hx.1, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ hx.2
theorem exact_cotMap {f : C →ₐc[R] A} (hf : Function.Surjective f) (g : D →ₐc[R] C)
    (hk : RingHom.ker f = kerIdeal g) : Function.Exact (cotMap g) (cotMap f) := by
  intro w
  constructor
  · intro hw
    obtain ⟨x, rfl⟩ := (AugCot.exact_kerMap_map (f : C →ₐ[R] A)
      (BialgHomClass.counitAlgHom_comp f) hf w).1 hw
    obtain ⟨v, hv⟩ := dUnit_mem_range_of_mem_kerIdeal g (hk.le x.2)
    exact ⟨v, hv.trans (AugCot.kerMap_apply _ _ x).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨a, rfl⟩ := AugCot.d_surjective _ v
    rw [cotMap_d, cotMap_d]
    have h := (kerIdeal_le_ker_iff g (f : C →ₐ[R] A)).1 hk.ge a
    exact (congrArg (dUnit R) h).trans (AugCot.d_algebraMap _ _)
theorem cotMap_mulBy [IsCocomm R C] (m : ℕ) (w : Cot R C) :
    cotMap (mulBy R C m) w = (m : R) • w := by
  rw [mulBy, cotMap_pow, ofConv_toConv, cotMap_id, Nat.cast_smul_eq_nsmul]
  rfl
theorem cotMap_eq_zero_iff [IsCocomm R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) {m : ℕ}
    (hk : RingHom.ker f = torsionIdeal R C m) (w : Cot R C) :
    cotMap f w = 0 ↔ ∃ v : Cot R C, w = (m : R) • v := by
  rw [exact_cotMap hf _ hk w]
  exact exists_congr fun v => by rw [cotMap_mulBy, eq_comm]
end PDiv
namespace PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
theorem cotMap_res_surjective (n : ℕ) : Function.Surjective (cotMap (G.res n)) :=
  cotMap_surjective (G.res_surjective n)
theorem cotMap_res_eq_zero_iff (n : ℕ) (w : Cot O (G.A (n + 1))) :
    cotMap (G.res n) w = 0 ↔ ∃ v, w = (p : O) ^ n • v := by
  rw [cotMap_eq_zero_iff (G.res_surjective n) (G.ker_res n), Nat.cast_pow]
def omegaLevel (n : ℕ) : G.omega →ₗ[O] Cot O (G.A n) :=
  LinearMap.proj n ∘ₗ G.omegaSub.subtype
@[simp] theorem omegaLevel_apply (n : ℕ) (w : G.omega) : G.omegaLevel n w = w.1 n := rfl
@[simp] theorem cotMap_res_omega (n : ℕ) (w : G.omega) :
    cotMap (G.res n) (w.1 (n + 1)) = w.1 n := w.2 n
theorem omega_val_eq_zero_of_le {m n : ℕ} (h : m ≤ n) {w : G.omega} (hw : w.1 n = 0) :
    w.1 m = 0 := by
  induction n, h using Nat.le_induction with
  | base => exact hw
  | succ n _ ih => exact ih (by rw [← w.2 n, hw, map_zero])
theorem cot_zero_eq_zero (w : Cot O (G.A 0)) : w = 0 := by
  simpa using G.pow_smul_cot 0 w
theorem omegaLevel_surjective (n : ℕ) : Function.Surjective (G.omegaLevel n) := by
  have hsec := fun k => (G.cotMap_res_surjective k).hasRightInverse
  choose s hs using hsec

  have key : ∀ (n : ℕ) (x : Cot O (G.A (n + 1))), cotMap (G.res n) x = 0 →
      ∃ w : G.omega, w.1 (n + 1) = x := by
    intro n x hx
    let u : ∀ k, Cot O (G.A k) := fun k =>
      if h : n + 1 ≤ k then Nat.leRecOn h (fun {k} => s k) x else 0
    refine ⟨⟨u, fun k => ?_⟩, by simp [u, Nat.leRecOn_self]⟩
    rcases lt_trichotomy k n with hk | rfl | hk
    · simp only [u]
      rw [dif_neg (by omega), dif_neg (by omega), map_zero]
    · simp only [u]
      rw [dif_pos le_rfl, dif_neg (by omega), Nat.leRecOn_self, hx]
    · simp only [u]
      rw [dif_pos (by omega), dif_pos (show n + 1 ≤ k from hk), Nat.leRecOn_succ (show n + 1 ≤ k from hk)]
      exact hs k _
  induction n with
  | zero => exact fun x => ⟨0, (G.cot_zero_eq_zero _).trans (G.cot_zero_eq_zero _).symm⟩
  | succ n ih =>
    intro x
    obtain ⟨v, hv⟩ := ih (cotMap (G.res n) x)
    obtain ⟨w, hw⟩ := key n (x - v.1 (n + 1)) (by rw [map_sub, v.2 n, ← hv]; exact sub_self _)
    refine ⟨w + v, ?_⟩
    rw [map_add, omegaLevel_apply, omegaLevel_apply, hw, sub_add_cancel]
theorem exists_sub_pow_smul_val_succ (n : ℕ) (w : G.omega) (hw : w.1 n = 0) :
    ∃ v : G.omega, (w - (p : O) ^ n • v).1 (n + 1) = 0 := by
  obtain ⟨x, hx⟩ := (G.cotMap_res_eq_zero_iff n (w.1 (n + 1))).1 ((w.2 n).trans hw)
  obtain ⟨v, rfl⟩ := G.omegaLevel_surjective (n + 1) x
  refine ⟨v, ?_⟩
  change w.1 (n + 1) - (p : O) ^ n • v.1 (n + 1) = 0
  rw [hx, omegaLevel_apply, sub_self]
theorem omega_val_eq_zero_iff (n : ℕ) (w : G.omega) :
    w.1 n = 0 ↔ ∃ v : G.omega, w = (p : O) ^ n • v := by
  refine ⟨fun hw => ?_, ?_⟩
  swap
  · rintro ⟨v, rfl⟩
    exact G.pow_smul_cot n (v.1 n)
  choose! c hc using G.exists_sub_pow_smul_val_succ
  let r : ℕ → G.omega := fun j => Nat.rec w (fun j x => x - (p : O) ^ (n + j) • c (n + j) x) j
  have hr : ∀ j, (r j).1 (n + j) = 0 := fun j => by
    induction j with
    | zero => exact hw
    | succ j ih => exact hc _ _ ih
  let t : ℕ → G.omega := fun k => ∑ j ∈ Finset.range k, (p : O) ^ j • c (n + j) (r j)
  have ht : ∀ k, w = r k + (p : O) ^ n • t k := fun k => by
    induction k with
    | zero => simp [t, r]
    | succ k ih =>
      have h1 : r (k + 1) = r k - (p : O) ^ (n + k) • c (n + k) (r k) := rfl
      have h2 : t (k + 1) = t k + (p : O) ^ k • c (n + k) (r k) := Finset.sum_range_succ _ _
      rw [h1, h2, smul_add, smul_smul, ← pow_add]
      exact ih.trans (by abel)
  refine ⟨⟨fun k => (t k).1 k, fun k => ?_⟩, Subtype.ext (funext fun k => ?_)⟩
  · have h2 : t (k + 1) = t k + (p : O) ^ k • c (n + k) (r k) := Finset.sum_range_succ _ _
    rw [(t (k + 1)).2 k, h2]
    change (t k).1 k + (p : O) ^ k • (c (n + k) (r k)).1 k = _
    rw [pow_smul_cot, add_zero]
  · have h := congrArg (fun x : G.omega => x.1 k) (ht k)
    refine h.trans ?_
    change (r k).1 k + (p : O) ^ n • (t k).1 k = (p : O) ^ n • (t k).1 k
    rw [G.omega_val_eq_zero_of_le (Nat.le_add_left k n) (hr k), zero_add]
theorem ker_omegaLevel (n : ℕ) :
    LinearMap.ker (G.omegaLevel n) = Ideal.span {(p : O)} ^ n • (⊤ : Submodule O G.omega) := by
  ext w
  rw [LinearMap.mem_ker, omegaLevel_apply, omega_val_eq_zero_iff, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]
def omegaQuotEquiv (n : ℕ) :
    (G.omega ⧸ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.omega)) ≃ₗ[O] Cot O (G.A n) :=
  Submodule.quotEquivOfEq _ _ (G.ker_omegaLevel n).symm ≪≫ₗ
    (G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)
@[simp] theorem omegaQuotEquiv_mk (n : ℕ) (w : G.omega) :
    G.omegaQuotEquiv n (Submodule.Quotient.mk w) = w.1 n := rfl
theorem omega_smodEq_iff (n : ℕ) (v w : G.omega) :
    v ≡ w [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.omega)] ↔ v.1 n = w.1 n := by
  rw [SModEq.sub_mem, ← ker_omegaLevel, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl
instance isAdicComplete_omega : IsAdicComplete (Ideal.span {(p : O)}) G.omega where
  haus' w hw := Subtype.ext (funext fun n => (G.omega_smodEq_iff n w 0).1 (hw n))
  prec' f hf := by
    refine ⟨⟨fun k => (f k).1 k, fun k => ?_⟩, fun n => (G.omega_smodEq_iff n _ _).2 rfl⟩
    rw [(f (k + 1)).2 k]
    exact ((G.omega_smodEq_iff k _ _).1 (hf (Nat.le_succ k))).symm
end PDivGroup
end GlobalTheory


