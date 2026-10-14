-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0598_parallel1
-- name    : PNT_ZeroFree_433_0598_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:20:41.74973+00:00
-- url     : https://prove2.me/theorems/506feadc-cf47-4587-8446-71deb7ec8008
-- title:
--   Zero-free region foundations: Inversion.InitialFibers [0598_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Inversion.InitialFibers
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Inversion/InitialFibers.lean#L13-L212

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0210
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Inversion/InitialFibers.lean#L13-L212
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Inversion.InitialFibers
section
namespace OAI

namespace SevenEighths.InverseInitialFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

@[ext] structure InitialTuple (J : ℕ) where
  common : Ideal O
  divisor : Ideal O
  residual : Ideal O
  frequency : O
  assigned : Fin J → SmoothMobiusCorrection.PrimeIdeal

structure Valid {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O) : Prop where
  common_eq : t * x.divisor = x.common
  label_eq : x.divisor * x.residual = f
  divisor_good : primaryGenerator x.divisor ≠ 0
  row_eq : primaryGenerator x.divisor * x.frequency = k
  assigned_dvd : ∀ i, (x.assigned i).val ∣ t * f

theorem Valid.of_reconstruction {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O)
    (hf : primaryGenerator f ≠ 0) (hC : t*x.divisor = x.common)
    (hlabel : x.divisor*x.residual = f)
    (hrow : primaryGenerator x.divisor*x.frequency = k)
    (hslots : ∀ i, (x.assigned i).val ∣ t*f) : Valid x t f k := by
  refine ⟨hC, hlabel, ?_, hrow, hslots⟩
  intro hz
  apply hf
  rw [← hlabel, primaryGenerator_mul, hz, zero_mul]

lemma divisor_dvd {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) : x.divisor ∣ f := ⟨x.residual, hx.label_eq.symm⟩

lemma divisor_ne_zero {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hf : f ≠ 0) : x.divisor ≠ 0 := by
  intro hz
  have he := hx.label_eq
  rw [hz, zero_mul] at he
  exact hf he.symm

theorem valid_key_injective {J : ℕ} (t f : Ideal O) (k : O) (hf : f ≠ 0)
    {x y : InitialTuple J} (hx : Valid x t f k) (hy : Valid y t f k)
    (hd : x.divisor = y.divisor) (ha : x.assigned = y.assigned) : x = y := by
  have hd0 := divisor_ne_zero hx hf
  have hc : x.common = y.common := by rw [← hx.common_eq, ← hy.common_eq, hd]
  have hs : x.residual = y.residual := by
    apply mul_left_cancel₀ hd0
    exact hx.label_eq.trans (by simpa only [hd] using hy.label_eq.symm)
  have hg : primaryGenerator x.divisor ≠ 0 := hx.divisor_good
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ hg
    exact hx.row_eq.trans (by simpa only [hd] using hy.row_eq.symm)
  exact InitialTuple.ext hc hd hs hr ha

lemma divisors_mul_image (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I*J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1*p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A,B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I*J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

theorem valid_tuple_card_le {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card * (idealDivisors (t*f)).card^J := by
  let D := idealDivisors f
  let E := idealDivisors (t*f)
  let encode (x : T) : D × (Fin J → E) :=
    (⟨x.val.divisor, (mem_idealDivisors hf).mpr (divisor_dvd (hT x.val x.property))⟩,
      fun i => ⟨(x.val.assigned i).val,
        (mem_idealDivisors (mul_ne_zero ht hf)).mpr ((hT x.val x.property).assigned_dvd i)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply valid_key_injective t f k hf (hT x.val x.property) (hT y.val y.property)
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) (congrFun (congrArg Prod.snd hxy) i)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, D, E] using Fintype.card_le_of_injective encode hi

theorem valid_tuple_card_le_separated {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card^(J+1) * (idealDivisors t).card^J := by
  apply (valid_tuple_card_le T t f k ht hf hT).trans
  calc
    _ ≤ (idealDivisors f).card *
        ((idealDivisors t).card * (idealDivisors f).card)^J :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (divisor_card_mul_le t f ht hf) J)
    _ = _ := by rw [mul_pow, pow_succ]; ring

lemma valid_label_squarefree {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hC : Squarefree x.common) (hs : Squarefree x.residual)
    (hmask : IsCoprime x.residual x.common) : Squarefree f := by
  have hdC : x.divisor ∣ x.common := by rw [← hx.common_eq]; exact dvd_mul_left _ _
  have hds : IsCoprime x.divisor x.residual := (hmask.of_isCoprime_of_dvd_right hdC).symm
  rw [← hx.label_eq]
  exact squarefree_mul_iff.mpr ⟨hds.isRelPrime, hC.squarefree_of_dvd hdC, hs⟩

lemma divisor_card_pos (I : Ideal O) (hI : I ≠ 0) : 1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

theorem valid_tuple_card_le_slot_cap {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) (K : ℕ) (hJ : J ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) := by
  apply (valid_tuple_card_le_separated T t f k ht hf hT).trans
  exact Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos t ht) hJ)

theorem valid_tuple_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (InitialTuple J)) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 → (∀ x ∈ T, Valid x t f k) →
      (T.card : ℝ) ≤ C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  have hJr : 0 < (J+1 : ℝ) := by positivity
  obtain ⟨C, hC, hb⟩ := IdealDivisorBound.ideal_divisor_small_power
    (ε/(J+1)) (div_pos hε hJr)
  refine ⟨C^(J+1), by positivity, ?_⟩
  intro T t f k ht hf hT
  have htf : t*f ≠ 0 := mul_ne_zero ht hf
  have hsub : idealDivisors f ⊆ idealDivisors (t*f) := by
    intro D hD
    exact (mem_idealDivisors htf).mpr
      (((mem_idealDivisors hf).mp hD).trans (dvd_mul_left _ _))
  have hcard : T.card ≤ (idealDivisors (t*f)).card^(J+1) := by
    apply (valid_tuple_card_le T t f k ht hf hT).trans
    calc
      _ ≤ (idealDivisors (t*f)).card * (idealDivisors (t*f)).card^J :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ = _ := by rw [pow_succ]; ring
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors (t*f)).card : ℝ))
    (hb (t*f) htf) (J+1)
  apply (show (T.card : ℝ) ≤ ((idealDivisors (t*f)).card : ℝ)^(J+1) by
    exact_mod_cast hcard).trans (hh.trans_eq ?_)
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), map_mul, Nat.cast_mul]
  congr 1
  push_cast
  field_simp

def initialFiber {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O) : Finset (InitialTuple J) :=
  source.filter (fun x => Valid x t f k ∧ (∀ i, x.assigned i ∈ lists i) ∧ keep x)

theorem initialFiber_card_le {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(J+1) * (idealDivisors t).card^J :=
  valid_tuple_card_le_separated _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_card_le_slot_cap {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (K : ℕ) (hJ : J ≤ 2*K) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) :=
  valid_tuple_card_le_slot_cap _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1) K hJ

theorem initialFiber_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (source : Finset (InitialTuple J))
      (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
      (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 →
      ((initialFiber source lists keep t f k).card : ℝ) ≤
        C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  obtain ⟨C, hC, hbound⟩ := valid_tuple_small_power J ε hε
  refine ⟨C, hC, ?_⟩
  intro source lists keep t f k ht hf
  exact hbound _ t f k ht hf (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_weight_bound {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (w : InitialTuple J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ initialFiber source lists keep t f k, ‖w x‖ ≤ C) :
    (∑ x ∈ initialFiber source lists keep t f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(J+1) * ((idealDivisors t).card : ℝ)^J := by
  calc
    _ ≤ ∑ _x ∈ initialFiber source lists keep t f k, C :=
      Finset.sum_le_sum hw
    _ = ((initialFiber source lists keep t f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(J+1) * (idealDivisors t).card^J : ℕ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast initialFiber_card_le source lists keep t f k ht hf) hC
    _ = _ := by push_cast; ring

end
end SevenEighths.InverseInitialFibers

end OAI

end


