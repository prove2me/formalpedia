-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:13.234848+00:00
-- url     : https://prove2.me/theorems/c48f43b3-32b4-41a3-81d3-651aeeacf09d
-- title:
--   Smul One Mem Unitary
-- statement:
--   Definitions and structural lemmas for Smul One Mem Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SmulOneMemUnitary.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_det_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_eq_zero_of_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_hasDerivAt_blockDet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_star_det_mul_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_submatrix_mul_blk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_continuous_toM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def epsHol (p q : ℕ) : Fin (p + q) → Bool := fun i => decide ((i : ℕ) < p)
def detWt (p q : ℕ) (a b : ℤ) : Fin (p + q) → ℝ := fun i => if (i : ℕ) < p then (a : ℝ) else (b : ℝ)
def blockDet {m : ℕ} (ε : Fin m → Bool) (s : Bool) (g : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  (g.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det
def blockTr {m : ℕ} (ε : Fin m → Bool) (s : Bool) (X : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ∑ a ∈ univ.filter (fun a => ε a = s), X a a
lemma toMK_one' (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl
lemma toMK_mul' {ε : Fin n → Bool} (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl
lemma toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ Kset ε := k.2
lemma blockDet_one (ε : Fin n → Bool) (s : Bool) : blockDet ε s 1 = 1 := by
  unfold blockDet
  rw [Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
lemma blockDet_mul_K {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (h : Matrix (Fin n) (Fin n) ℂ) : blockDet ε s (g * h) = blockDet ε s g * blockDet ε s h := by
  unfold blockDet
  rw [InhabA.submatrix_mul_blk s (fun i j hij => InhabA.eq_zero_of_comm hg.2 i j hij) h, Matrix.det_mul]
lemma blockDet_ne_zero {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    blockDet ε s g ≠ 0 := InhabA.det_ne_zero s hg
lemma star_blockDet_mul {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    star (blockDet ε s g) * blockDet ε s g = 1 := InhabA.star_det_mul_det s hg
lemma star_char_mul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (a b : ℤ) :
    star (blockDet ε true g ^ a * blockDet ε false g ^ b) * (blockDet ε true g ^ a * blockDet ε false g ^ b)
      = 1 := by
  have h1 := star_blockDet_mul true hg
  have h2 := star_blockDet_mul false hg
  rw [star_mul', star_zpow₀, star_zpow₀]
  calc star (blockDet ε true g) ^ a * star (blockDet ε false g) ^ b *
        (blockDet ε true g ^ a * blockDet ε false g ^ b)
      = (star (blockDet ε true g) * blockDet ε true g) ^ a *
          (star (blockDet ε false g) * blockDet ε false g) ^ b := by
        rw [mul_zpow, mul_zpow]; ring
    _ = 1 := by rw [h1, h2, _root_.one_zpow, _root_.one_zpow, one_mul]
lemma smul_one_mem_unitary {c : ℂ} (hc : star c * c = 1) : c • (1 : ℂ →L[ℂ] ℂ) ∈ unitary (ℂ →L[ℂ] ℂ) := by
  have hc1 : (starRingEnd ℂ) c * c = 1 := hc
  have hc2 : c * (starRingEnd ℂ) c = 1 := by rw [mul_comm]; exact hc
  rw [Unitary.mem_iff]
  constructor <;> simp [star_smul, smul_smul, hc1, hc2]
lemma blockTr_add {m : ℕ} (ε : Fin m → Bool) (s : Bool) (X Y : Matrix (Fin m) (Fin m) ℂ) :
    blockTr ε s (X + Y) = blockTr ε s X + blockTr ε s Y := by
  simp [blockTr, Finset.sum_add_distrib]
lemma blockTr_smul {m : ℕ} (ε : Fin m → Bool) (s : Bool) (c : ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    blockTr ε s (c • X) = c * blockTr ε s X := by
  simp [blockTr, Finset.mul_sum]
lemma blockTr_single_diag {m : ℕ} (ε : Fin m → Bool) (s : Bool) (i : Fin m) :
    blockTr ε s (Matrix.single i i 1) = if ε i = s then 1 else 0 := by
  simp [blockTr, Matrix.single_apply]
lemma blockTr_single_ne {m : ℕ} (ε : Fin m → Bool) (s : Bool) {i j : Fin m} (hij : i ≠ j) :
    blockTr ε s (Matrix.single i j 1) = 0 := by
  unfold blockTr
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.single_apply]
  exact if_neg fun h => hij (h.1.trans h.2.symm)
def detKType (p q : ℕ) (a b : ℤ) : KType (epsHol p q) (detWt p q a b) where
  V := ℂ
  τ :=
    { toFun := fun k => ⟨(blockDet (epsHol p q) true (toMK k) ^ a *
          blockDet (epsHol p q) false (toMK k) ^ b) • (1 : ℂ →L[ℂ] ℂ),
          smul_one_mem_unitary (star_char_mul (toMK_mem _ k) a b)⟩
      map_one' := by
        apply Subtype.ext
        show (blockDet (epsHol p q) true (toMK (1 : KG (epsHol p q))) ^ a *
          blockDet (epsHol p q) false (toMK (1 : KG (epsHol p q))) ^ b) • (1 : ℂ →L[ℂ] ℂ) = 1
        rw [toMK_one', blockDet_one, blockDet_one, _root_.one_zpow, _root_.one_zpow, one_mul, one_smul]
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (blockDet (epsHol p q) true (toMK (x * y)) ^ a *
          blockDet (epsHol p q) false (toMK (x * y)) ^ b) • (1 : ℂ →L[ℂ] ℂ) =
          ((blockDet (epsHol p q) true (toMK x) ^ a * blockDet (epsHol p q) false (toMK x) ^ b) •
            (1 : ℂ →L[ℂ] ℂ)) *
          ((blockDet (epsHol p q) true (toMK y) ^ a * blockDet (epsHol p q) false (toMK y) ^ b) •
            (1 : ℂ →L[ℂ] ℂ))
        rw [toMK_mul', blockDet_mul_K true (toMK_mem _ x), blockDet_mul_K false (toMK_mem _ x),
          smul_mul_smul_comm, one_mul, mul_zpow, mul_zpow, mul_mul_mul_comm] }
  cont := by
    have hK : Continuous (fun k : KG (epsHol p q) => toMK k) :=
      (continuous_toM _).comp continuous_subtype_val
    have hd : ∀ s : Bool, Continuous (fun k : KG (epsHol p q) => blockDet (epsHol p q) s (toMK k)) :=
      fun s => (hK.matrix_submatrix _ _).matrix_det
    refine Continuous.subtype_mk ?_ _
    exact (((hd true).zpow₀ a (fun k => Or.inl (blockDet_ne_zero true (toMK_mem _ k)))).mul
      ((hd false).zpow₀ b (fun k => Or.inl (blockDet_ne_zero false (toMK_mem _ k))))).smul
      continuous_const
  irred := fun W _ => Ideal.eq_bot_or_top W
  dτ :=
    { toFun := fun X => ((a : ℂ) * blockTr (epsHol p q) true X + (b : ℂ) * blockTr (epsHol p q) false X) •
          (1 : ℂ →L[ℂ] ℂ)
      map_add' := by
        intro X Y
        rw [blockTr_add, blockTr_add, ← add_smul]
        congr 1
        ring
      map_smul' := by
        intro c X
        rw [blockTr_smul, blockTr_smul, RingHom.id_apply, smul_smul]
        congr 1
        ring }
  hasDeriv := by
    intro X _ γ hγ
    have hF : ∀ s : Bool, HasDerivAt (fun t : ℝ => blockDet (epsHol p q) s
        (NormedSpace.exp ((t : ℂ) • X))) (blockTr (epsHol p q) s X) 0 :=
      fun s => InhabA.hasDerivAt_blockDet (epsHol p q) s X
    have hF0 : ∀ s : Bool, blockDet (epsHol p q) s (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
      intro s
      rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, blockDet_one]
    have hZ : ∀ (s : Bool) (e : ℤ), HasDerivAt (fun t : ℝ => blockDet (epsHol p q) s
        (NormedSpace.exp ((t : ℂ) • X)) ^ e) ((e : ℂ) * blockTr (epsHol p q) s X) 0 := by
      intro s e
      have h := (hasDerivAt_zpow e _ (Or.inl (by rw [hF0 s]; exact one_ne_zero))).comp (0 : ℝ) (hF s)
      rw [hF0 s, _root_.one_zpow, mul_one] at h
      exact h
    have hP := ((hZ true a).mul (hZ false b)).smul_const (1 : ℂ →L[ℂ] ℂ)
    rw [hF0 true, hF0 false, _root_.one_zpow, _root_.one_zpow, one_mul, mul_one] at hP
    have hfun : (fun t : ℝ => ((blockDet (epsHol p q) true (toMK (γ t)) ^ a *
        blockDet (epsHol p q) false (toMK (γ t)) ^ b) • (1 : ℂ →L[ℂ] ℂ))) =
        (fun t : ℝ => (blockDet (epsHol p q) true (NormedSpace.exp ((t : ℂ) • X)) ^ a *
        blockDet (epsHol p q) false (NormedSpace.exp ((t : ℂ) • X)) ^ b) • (1 : ℂ →L[ℂ] ℂ)) := by
      funext t
      rw [hγ t]
    show HasDerivAt (fun t : ℝ => ((blockDet (epsHol p q) true (toMK (γ t)) ^ a *
        blockDet (epsHol p q) false (toMK (γ t)) ^ b) • (1 : ℂ →L[ℂ] ℂ))) _ 0
    rw [hfun]
    exact hP
  w := 1
  w_norm := by simp
  w_wt := by
    intro i
    show (((a : ℂ) * blockTr (epsHol p q) true (Matrix.single i i 1) +
      (b : ℂ) * blockTr (epsHol p q) false (Matrix.single i i 1)) • (1 : ℂ →L[ℂ] ℂ)) 1 =
      ((detWt p q a b i : ℝ) : ℂ) • (1 : ℂ)
    rw [blockTr_single_diag, blockTr_single_diag]
    by_cases h : (i : ℕ) < p
    · simp [epsHol, detWt, h]
    · simp [epsHol, detWt, h]
  w_hw := by
    intro i j hij _
    show (((a : ℂ) * blockTr (epsHol p q) true (Matrix.single i j 1) +
      (b : ℂ) * blockTr (epsHol p q) false (Matrix.single i j 1)) • (1 : ℂ →L[ℂ] ℂ)) 1 = 0
    rw [blockTr_single_ne _ _ (ne_of_lt hij), blockTr_single_ne _ _ (ne_of_lt hij)]
    simp
end ReciprocityTheory.ChartRestriction.DS.S7


