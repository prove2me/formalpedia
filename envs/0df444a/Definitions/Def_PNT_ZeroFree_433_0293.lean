-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0293
-- name    : PNT_ZeroFree_433_0293
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:25:32.494641+00:00
-- url     : https://prove2.me/theorems/e7e1218d-3ae1-4cda-923b-9982caccddb6
-- title:
--   Zero-free region foundations: Moments.Canonical, Moments.FullCorrelation, Moments.CommonSupport [0293]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Moments.Canonical
--   - OAI.NumberTheory.DirichletL.Moments.FullCorrelation
--   - OAI.NumberTheory.DirichletL.Moments.CommonSupport
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/Canonical.lean#L14-L128
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/FullCorrelation.lean#L11-L178
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/CommonSupport.lean#L12-L234

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.NNReal.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0150
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0292_parallel1
import Definitions.Def_PNT_ZeroFree_433_0293_parallel1
import Definitions.Def_PNT_ZeroFree_433_0294_parallel1
import Definitions.Def_PNT_ZeroFree_433_0306_parallel1
import Definitions.Def_PNT_ZeroFree_433_0326_parallel1
import Definitions.Def_PNT_ZeroFree_433_0339_parallel1
import Definitions.Def_PNT_ZeroFree_433_0366_parallel1
import Definitions.Def_PNT_ZeroFree_433_0369_parallel1
import Definitions.Def_PNT_ZeroFree_433_0391_parallel1
import Definitions.Def_PNT_ZeroFree_433_0439_parallel1
import Definitions.Def_PNT_ZeroFree_433_0464_parallel1
import Definitions.Def_PNT_ZeroFree_433_0480_parallel1
import Definitions.Def_PNT_ZeroFree_433_0600_parallel1
import Definitions.Def_PNT_ZeroFree_433_0616_parallel1
import Definitions.Def_PNT_ZeroFree_433_0623_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/Canonical.lean#L14-L128
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/FullCorrelation.lean#L11-L178
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/CommonSupport.lean#L12-L234
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Moments.Canonical
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

def primePowerRow (P : Ideal O) [P.IsMaximal] (hg : goodLambda ∉ P)
    {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) : ℂ :=
  (actualSextic P hg ^ c) (primePowerReduction P hc x)

theorem canonical_primePower_units (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    fullCorrelation (fun x => v * x) (fun y => (u : O ⧸ P ^ c) * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      actualSextic P hg (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) :=
  primePower_localCorrelation_units P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hv

theorem canonical_primePower_second_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : O ⧸ P ^ c) * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_second_zero P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hv

theorem canonical_primePower_first_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : O ⧸ P ^ c) (v : (O ⧸ P ^ c)ˣ) (k : O ⧸ P ^ c)
    (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : O ⧸ P ^ c) * x) (fun y => u * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_first_zero P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hu

def canonicalPrimePowerCharacter (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) : MulChar (O ⧸ P ^ c) ℂ :=
  primePowerCharacter P hc (actualSextic P hg ^ c)

theorem canonicalPrimePowerCharacter_mk (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O) :
    canonicalPrimePowerCharacter P hg hc (Ideal.Quotient.mk (P ^ c) x) =
      CanonicalRowCompletion.idealRowHom x (P ^ c) := by
  change (actualSextic P hg ^ c) (Ideal.Quotient.mk P x) = _
  rw [MulChar.pow_apply' _ (by omega), map_pow,
    CanonicalRowCompletion.idealRowHom_prime x P hg]

private theorem pairwise_isCoprime_pow {ι : Type*}
    (P : ι → Ideal O) (c : ι → ℕ)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
  intro i j hij
  exact (hcop hij).pow

def canonicalCRTCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ ∏ i, P i ^ c i) ℂ :=
  crtCharacter (IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
    (pairwise_isCoprime_pow P c hcop))
    (fun i => canonicalPrimePowerCharacter (P i) (hg i) (hc i))

theorem canonicalCRTCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    canonicalCRTCharacter P hg c hc hcop (Ideal.Quotient.mk (∏ i, P i ^ c i) x) =
      CanonicalRowCompletion.idealRowHom x (∏ i, P i ^ c i) := by
  simp only [canonicalCRTCharacter, crtCharacter_apply,
    IdealGaussCRT.quotientProdEquivPi_mk, canonicalPrimePowerCharacter_mk, map_prod]

theorem canonicalCRTCorrelation {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i ^ c i)] [∀ i, Fintype (O ⧸ P i ^ c i)]
    (u v k : O ⧸ ∏ i, P i ^ c i) :
    let e := IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
      (pairwise_isCoprime_pow P c hcop)
    fullCorrelation (fun x => v * x) (fun y => u * y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (e k i) := by
  dsimp only
  change fullCorrelation (fun x => v * x) (fun y => u * y)
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i)) k = _
  rw [fullCorrelation_ringEquiv (IdealGaussCRT.quotientProdEquivPi _ _) u v k
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i)), fullCorrelation_pi]

end SevenEighths.CenteredMomentCanonical
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Moments.FullCorrelation
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

def scaledResidue (d a m : A) (hm : m = d * a) :
    (A ⧸ Ideal.span {d}) → (A ⧸ Ideal.span {m}) := fun x =>
  Quotient.liftOn' x (fun z => Ideal.Quotient.mk (Ideal.span {m}) (a * z)) (by
    intro x y hxy
    apply Ideal.Quotient.eq.mpr
    have hd : d ∣ x - y := Ideal.mem_span_singleton.mp
      ((Ideal.span {d}).quotientRel_def.mp hxy)
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    rw [hm, ← mul_sub, hz]
    ring)

@[simp] theorem scaledResidue_mk (d a m : A) (hm : m = d * a) (x : A) :
    scaledResidue d a m hm (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {m}) (a * x) := rfl

def fullModulusCorrelation (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A) : ℂ :=
  fullCorrelation (scaledResidue u v (u * v) rfl)
    (scaledResidue v u (u * v) (mul_comm u v)) χu χv
    (Ideal.Quotient.mk (Ideal.span {u * v}) j)

theorem scaledResidue_congruence (u v x y j : A) :
    scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) x) -
      scaledResidue v u (u * v) (mul_comm u v)
        (Ideal.Quotient.mk (Ideal.span {v}) y) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j ↔
      u * v ∣ v * x - u * y - j := by
  rw [scaledResidue_mk, scaledResidue_mk, ← map_sub, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton

theorem fullModulusCorrelation_fourier (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    [Fintype (A ⧸ Ideal.span {u * v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A)
    (ψ : AddChar (A ⧸ Ideal.span {u * v}) ℂ) (hψ : ψ.IsPrimitive) :
    (∑ h : A ⧸ Ideal.span {u * v},
      fourierSum ψ (scaledResidue u v (u * v) rfl) χu h *
        star (fourierSum ψ (scaledResidue v u (u * v) (mul_comm u v)) χv h) *
          ψ (-(h * Ideal.Quotient.mk (Ideal.span {u * v}) j))) =
      (Fintype.card (A ⧸ Ideal.span {u * v}) : ℂ) * fullModulusCorrelation u v χu χv j :=
  fullCorrelation_fourier ψ hψ _ _ χu χv _

theorem common_divisor_frequency {u v d x y j : A}
    (hdu : d ∣ u) (hdv : d ∣ v) (hcong : u * v ∣ v * x - u * y - j) : d ∣ j := by
  have hleft : d ∣ v * x - u * y := dvd_sub (hdv.trans (dvd_mul_right v x))
    (hdu.trans (dvd_mul_right u y))
  have hprod : d ∣ u * v := hdu.trans (dvd_mul_right u v)
  have hdiff := dvd_sub hleft (hprod.trans hcong)
  convert! hdiff using 1 ; ring

theorem fullModulusCorrelation_eq_zero_of_common_not_dvd (u v d j : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hdu : d ∣ u) (hdv : d ∣ v) (hdj : ¬d ∣ j) :
    fullModulusCorrelation u v χu χv j = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  have hn : ¬ scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j := by
    intro h
    exact hdj (common_divisor_frequency hdu hdv ((scaledResidue_congruence u v a b j).mp h))
  exact if_neg hn

theorem dvd_of_unit_residue_mul {u x v : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x)) (hdiv : u ∣ v * x) : u ∣ v := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hm : Ideal.Quotient.mk (Ideal.span {u}) v *
      Ideal.Quotient.mk (Ideal.span {u}) x = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  exact hx.mul_right_injective (by simpa only [mul_comm, mul_zero, zero_mul] using hm)

theorem zero_frequency_units_force_divides {u v x y : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x))
    (hy : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) y))
    (hcong : u * v ∣ v * x - u * y) : u ∣ v ∧ v ∣ u := by
  have hu : u ∣ v * x := by
    have h := dvd_add ((dvd_mul_right u v).trans hcong) (dvd_mul_right u y)
    simpa only [sub_add_cancel] using h
  have hv : v ∣ u * y := by
    have h := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hcong)
    convert! h using 1 ; ring
  exact ⟨dvd_of_unit_residue_mul hx hu, dvd_of_unit_residue_mul hy hv⟩

theorem fullModulusCorrelation_zero_frequency_off_diagonal (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hne : Ideal.span ({u} : Set A) ≠ Ideal.span ({v} : Set A)) :
    fullModulusCorrelation u v χu χv 0 = 0 := by
  classical
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  change (if scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) 0
    then χu (Ideal.Quotient.mk (Ideal.span {u}) a) *
      star (χv (Ideal.Quotient.mk (Ideal.span {v}) b)) else 0) = 0
  by_cases hx : χu (Ideal.Quotient.mk (Ideal.span {u}) a) = 0
  · simp only [hx, zero_mul, ite_self]
  by_cases hy : χv (Ideal.Quotient.mk (Ideal.span {v}) b) = 0
  · simp only [hy, star_zero, mul_zero, ite_self]
  split_ifs with h
  · exfalso
    have hd := (scaledResidue_congruence u v a b 0).mp h
    rw [sub_zero] at hd
    obtain ⟨huv, hvu⟩ := zero_frequency_units_force_divides
      (χu.apply_ne_zero_iff.mp hx) (χv.apply_ne_zero_iff.mp hy) hd
    apply hne
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr hvu
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr huv
  · rfl

variable [IsDomain A]

theorem scaledResidue_injective (d a m : A) (hm : m = d * a) (ha : a ≠ 0) :
    Function.Injective (scaledResidue d a m hm) := by
  intro x y
  refine Quotient.inductionOn₂' x y ?_
  intro r s hrs
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hrs)
  change m ∣ a * r - a * s at hd
  rw [hm, ← mul_sub, mul_comm d a] at hd
  exact (mul_dvd_mul_iff_left ha).mp hd

theorem fullModulusCorrelation_zero_frequency_diagonal (u : A) (hu : u ≠ 0)
    [Fintype (A ⧸ Ideal.span {u})] (χ : MulChar (A ⧸ Ideal.span {u}) ℂ) :
    fullModulusCorrelation u u χ χ 0 =
      (Fintype.card (A ⧸ Ideal.span {u})ˣ : ℂ) := by
  classical
  have hinj := scaledResidue_injective u u (u * u) rfl hu
  unfold fullModulusCorrelation fullCorrelation
  have hcond (x y : A ⧸ Ideal.span {u}) :
      scaledResidue u u (u * u) rfl x -
        scaledResidue u u (u * u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u * u}) 0 ↔ y = x := by
    rw [map_zero, sub_eq_zero]
    exact hinj.eq_iff.trans eq_comm
  simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.sum_one_eq_card_units

end SevenEighths.CenteredMomentCorrelation
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Moments.CommonSupport
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

abbrev Residue (d : A) := A ⧸ Ideal.span {d}

def principalCRT (d a : A) (h : IsCoprime d a) :
    Residue (d * a) ≃+* Residue d × Residue a :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton d a).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {d}) (Ideal.span {a})
      ((Ideal.isCoprime_span_singleton_iff d a).mpr h))

@[simp] theorem principalCRT_mk (d a : A) (h : IsCoprime d a) (x : A) :
    principalCRT d a h (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
  ext <;> simp [principalCRT, Ideal.quotEquivOfEq_mk]

lemma coprime_mul_dvd_iff (d a n : A) (h : IsCoprime d a) :
    d * a ∣ n ↔ d ∣ n ∧ a ∣ n := by
  constructor
  · intro hn
    exact ⟨(dvd_mul_right d a).trans hn, (dvd_mul_left a d).trans hn⟩
  · rintro ⟨hd, ha⟩
    exact h.mul_dvd hd ha

theorem full_product_congruence (D E a b n : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ n ↔ D * E ∣ n ∧ a ∣ n ∧ b ∣ n := by
  have heq : (D * a) * (E * b) = (D * E) * (a * b) := by ring
  rw [heq, coprime_mul_dvd_iff _ _ _ (ha.mul_right hb), coprime_mul_dvd_iff _ _ _ hab]

theorem isUnit_residue_of_coprime (d a : A) (h : IsCoprime d a) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {d}) a) := by
  obtain ⟨u, v, huv⟩ := h
  apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (Ideal.span {d}) v)
  have hd : Ideal.Quotient.mk (Ideal.span {d}) d = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {d})) huv
  simpa only [map_add, map_mul, map_one, hd, mul_zero, zero_mul, zero_add, mul_comm] using hm

lemma residue_eq_zero_iff_dvd (d n : A) :
    Ideal.Quotient.mk (Ideal.span {d}) n = 0 ↔ d ∣ n := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem full_congruence_split (D E a b x y j : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ (E * b) * x - (D * a) * y - j ↔
      (D * E ∣ E * (b * x) - D * (a * y) - j) ∧
      Ideal.Quotient.mk (Ideal.span {a}) (E * b * x) = Ideal.Quotient.mk _ j ∧
      Ideal.Quotient.mk (Ideal.span {b}) (D * a * y) = Ideal.Quotient.mk _ (-j) := by
  rw [full_product_congruence D E a b _ ha hb hab]
  have hzeroa : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  have hzerob : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  have heq : (E * b) * x - (D * a) * y - j = E * (b * x) - D * (a * y) - j := by ring
  refine and_congr (by rw [heq]) (and_congr ?_ ?_)
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzeroa, mul_zero, zero_mul, sub_zero]
    exact sub_eq_zero
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzerob, mul_zero, zero_mul, zero_sub, map_neg]
    constructor <;> intro h <;> linear_combination -h

theorem sum_residual_constraints
    {X Y S T : Type*} [Fintype X] [Fintype Y] [CommRing S] [CommRing T]
    [Fintype S] [Fintype T]
    (p : X → Y → Prop) [∀ x y, Decidable (p x y)]
    (f : X → ℂ) (g : Y → ℂ) (α : S → ℂ) (β : T → ℂ)
    (a : Sˣ) (b : Tˣ) (j : S) (k : T) :
    (∑ x : X × S, ∑ y : Y × T,
      if p x.1 y.1 ∧ (a : S) * x.2 = j ∧ (b : T) * y.2 = k
      then (f x.1 * α x.2) * star (g y.1 * β y.2) else 0) =
    (∑ x : X, ∑ y : Y, if p x y then f x * star (g y) else 0) *
      α ((↑a⁻¹ : S) * j) * star (β ((↑b⁻¹ : T) * k)) := by
  have ha (x : S) : (a : S) * x = j ↔ x = (↑a⁻¹ : S) * j := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  have hb (y : T) : (b : T) * y = k ↔ y = (↑b⁻¹ : T) * k := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  simp only [Fintype.sum_prod_type, ha, hb]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p x y
  · simp only [h, true_and, star_mul]
    simp [ite_and, Finset.sum_ite_eq', mul_assoc, mul_left_comm, mul_comm]
  · simp [h]

theorem fullCorrelation_unit_change
    {X Y R : Type*} [CommRing X] [CommRing Y] [CommRing R]
    [Fintype X] [Fintype Y]
    (left : X → R) (right : Y → R) (χ : MulChar X ℂ) (ψ : MulChar Y ℂ)
    (u : Xˣ) (v : Yˣ) (j : R) :
    fullCorrelation (fun x => left ((u : X) * x)) (fun y => right ((v : Y) * y)) χ ψ j =
      χ (↑u⁻¹ : X) * star (ψ (↑v⁻¹ : Y)) * fullCorrelation left right χ ψ j := by
  have hχ (x : X) : χ x = χ (↑u⁻¹ : X) * χ ((u : X) * x) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hψ (y : Y) : ψ y = ψ (↑v⁻¹ : Y) * ψ ((v : Y) * y) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  unfold fullCorrelation
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv u.mulLeft
  intro x
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv v.mulLeft
  intro y
  simp only [Units.mulLeft_apply]
  by_cases h : left ((u : X) * x) - right ((v : Y) * y) = j
  · simp only [h, ite_true]
    rw [hχ x, hψ y, star_mul]
    ring
  · simp only [h, ite_false, mul_zero]

lemma character_unit_inverse {X : Type*} [CommRing X] [Fintype X]
    (χ : MulChar X ℂ) (u : Xˣ) : χ (↑u⁻¹ : X) = star (χ (u : X)) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

def residueUnit (d a : A) (h : IsCoprime d a) : (Residue d)ˣ :=
  (isUnit_residue_of_coprime d a h).unit

@[simp] theorem residueUnit_coe (d a : A) (h : IsCoprime d a) :
    (residueUnit d a h : Residue d) = Ideal.Quotient.mk _ a :=
  (isUnit_residue_of_coprime d a h).unit_spec

def scaledCommonCorrelation (D E a b : A)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) : ℂ :=
  fullCorrelation
    (fun x => scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x))
    (fun y => scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y))
    χD χE (Ideal.Quotient.mk _ j)

theorem scaledCommonCorrelation_eq (D E a b : A)
    (hDb : IsCoprime D b) (hEa : IsCoprime E a)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) :
    scaledCommonCorrelation D E a b χD χE j =
      star (χD (Ideal.Quotient.mk _ b)) * χE (Ideal.Quotient.mk _ a) *
        fullModulusCorrelation D E χD χE j := by
  have h := fullCorrelation_unit_change
    (scaledResidue D E (D * E) rfl) (scaledResidue E D (D * E) (mul_comm _ _))
    χD χE (residueUnit D b hDb) (residueUnit E a hEa) (Ideal.Quotient.mk _ j)
  simpa only [residueUnit_coe, character_unit_inverse, star_star,
    scaledCommonCorrelation, fullModulusCorrelation] using h

theorem fullModulusCorrelation_extract (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
    let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      scaledCommonCorrelation D E a b χD χE j *
        χa ((↑α⁻¹ : Residue a) * Ideal.Quotient.mk _ j) *
        star (χb ((↑β⁻¹ : Residue b) * Ideal.Quotient.mk _ (-j))) := by
  dsimp only
  let e₁ := principalCRT D a (IsCoprime.mul_left_iff.mp ha).1
  let e₂ := principalCRT E b (IsCoprime.mul_left_iff.mp hb).2
  let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
  let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
  let p := fun x : Residue D => fun y : Residue E =>
    scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x) -
      scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y) =
        Ideal.Quotient.mk _ j
  have hextract : fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      ∑ x : Residue D × Residue a, ∑ y : Residue E × Residue b,
        if p x.1 y.1 ∧ (α : Residue a) * x.2 = Ideal.Quotient.mk _ j ∧
          (β : Residue b) * y.2 = Ideal.Quotient.mk _ (-j)
        then (χD x.1 * χa x.2) * star (χE y.1 * χb y.2) else 0 := by
    unfold fullModulusCorrelation fullCorrelation
    apply Fintype.sum_equiv e₁.toEquiv
    intro x
    apply Fintype.sum_equiv e₂.toEquiv
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [e₁, e₂, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, principalCRT_mk,
      hχDa, hχEb, p, α, β, residueUnit_coe, ← map_mul]
    rw [scaledResidue_congruence, scaledResidue_congruence,
      full_congruence_split D E a b x y j ha hb hab]
    split_ifs <;> rfl
  rw [hextract, sum_residual_constraints]
  rfl

theorem fullModulusCorrelation_complete_support (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      fullModulusCorrelation D E χD χE j *
        (χE (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ E))) *
        (χb (Ideal.Quotient.mk _ D) * star (χD (Ideal.Quotient.mk _ b))) *
        (χb (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ b))) *
        χa (Ideal.Quotient.mk _ j) * star (χb (Ideal.Quotient.mk _ (-j))) := by
  rw [fullModulusCorrelation_extract D E a b ha hb hab χD χE χa χb χDa χEb hχDa hχEb j]
  rw [scaledCommonCorrelation_eq D E a b (IsCoprime.mul_left_iff.mp hb).1
    (IsCoprime.mul_left_iff.mp ha).2 χD χE j]
  simp only [map_mul, character_unit_inverse, residueUnit_coe, star_mul, star_star]
  ring

end SevenEighths.CenteredMomentCommonSupport
end

end OAI

end


