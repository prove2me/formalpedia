-- Prove2me | Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
-- name    : LeanPool_Egrs75_CentralBinomialDigits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:18.674954+00:00
-- url     : https://prove2.me/theorems/5fbcaeb1-918b-4df4-a871-6f400dbb5544
-- title:
--   Central Binomial Digits
-- statement:
--   Definitions and structural lemmas for Central Binomial Digits, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/CentralBinomialDigits.lean

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Definitions.Def_LeanPool_Egrs75_KummerValuation
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Theorems.Thm_Egrs75_ConcreteMath_sub_one_mul_padicValNat_centralBinom

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.Erdos376
open Nat
def LowDoubleDigits (p n : ℕ) : Prop := ∀ d ∈ Nat.digits p n, 2 * d < p
def doubleCarryStep (b carry d : ℕ) : ℕ := if b ≤ 2 * d + carry then 1 else 0
def doubleDigitsAux (b : ℕ) : List ℕ → ℕ → List ℕ
  | [], carry => [carry]
  | d :: ds, carry =>
      (2 * d + carry) % b :: doubleDigitsAux b ds (doubleCarryStep b carry d)
def doubleCarryCountAux (b : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | d :: ds, carry =>
      let next := doubleCarryStep b carry d
      next + doubleCarryCountAux b ds next
def doubleCarryCount (b : ℕ) (ds : List ℕ) : ℕ := doubleCarryCountAux b ds 0
lemma doubleCarryStep_le_one (b carry d : ℕ) : doubleCarryStep b carry d ≤ 1 := by
  unfold doubleCarryStep; split <;> simp
lemma doubleDigitsAux_length (b : ℕ) :
    ∀ (ds : List ℕ) (carry : ℕ),
      (doubleDigitsAux b ds carry).length = ds.length + 1 := by
  intro ds
  induction ds with
  | nil => intro carry; simp [doubleDigitsAux]
  | cons d ds ih => intro carry; simp [doubleDigitsAux, ih, Nat.add_comm]
lemma doubleCarryStep_eq_div {b carry d : ℕ} (_hb : 2 ≤ b)
    (hcarry : carry ≤ 1) (hd : d < b) :
    doubleCarryStep b carry d = (2 * d + carry) / b := by
  unfold doubleCarryStep
  -- `2d + carry < 2b`, so the quotient by `b` is `0` or `1`, matching the test.
  have hlt : 2 * d + carry < 2 * b := by omega
  by_cases h : b ≤ 2 * d + carry
  · simp only [h, ite_true]
    have h1 : (2 * d + carry) / b = 1 := by
      rw [Nat.div_eq_of_lt_le] <;> omega
    omega
  · simp only [h, ite_false]
    have : (2 * d + carry) / b = 0 := Nat.div_eq_of_lt (by omega)
    omega
lemma doubleCarryStep_local {b carry d : ℕ} (hb : 2 ≤ b)
    (hcarry : carry ≤ 1) (hd : d < b) :
    (2 * d + carry) % b + b * doubleCarryStep b carry d = 2 * d + carry := by
  rw [doubleCarryStep_eq_div hb hcarry hd]
  exact Nat.mod_add_div (2 * d + carry) b
lemma doubleDigitsAux_lt_base {b : ℕ} (hb : 2 ≤ b) :
    ∀ {ds : List ℕ} {carry : ℕ}, carry < b → (∀ d ∈ ds, d < b) →
      ∀ x ∈ doubleDigitsAux b ds carry, x < b := by
  intro ds
  induction ds with
  | nil =>
      intro carry hcarry _ x hx
      have : x = carry := by simpa [doubleDigitsAux] using hx
      simpa [this] using hcarry
  | cons d ds ih =>
      intro carry hcarry hds x hx
      have hd : d < b := hds d List.mem_cons_self
      have htail : ∀ e ∈ ds, e < b := fun e he => hds e (List.mem_cons_of_mem d he)
      have hx' : x = (2 * d + carry) % b ∨
          x ∈ doubleDigitsAux b ds (doubleCarryStep b carry d) := by
        simpa [doubleDigitsAux] using hx
      rcases hx' with hx | hx
      · rw [hx]; exact Nat.mod_lt _ (by omega)
      · have hnext : doubleCarryStep b carry d < b := by
          have := doubleCarryStep_le_one b carry d; omega
        exact ih hnext htail x hx
lemma doubleDigitsAux_ofDigits {b : ℕ} (hb : 2 ≤ b) :
    ∀ {ds : List ℕ} {carry : ℕ}, carry ≤ 1 → (∀ d ∈ ds, d < b) →
      Nat.ofDigits b (doubleDigitsAux b ds carry) =
        2 * Nat.ofDigits b ds + carry := by
  intro ds
  induction ds with
  | nil => intro carry _ _; simp [doubleDigitsAux, Nat.ofDigits]
  | cons d ds ih =>
      intro carry hcarry hds
      have hd : d < b := hds d List.mem_cons_self
      have htail : ∀ e ∈ ds, e < b := fun e he => hds e (List.mem_cons_of_mem d he)
      have hnext : doubleCarryStep b carry d ≤ 1 := doubleCarryStep_le_one b carry d
      have hlocal := doubleCarryStep_local hb hcarry hd
      rw [doubleDigitsAux, Nat.ofDigits_cons, ih hnext htail, Nat.ofDigits_cons]
      -- goal: (2d+carry)%b + b*(2*ofDigits ds + carryStep) = 2*(d + b*ofDigits ds) + carry
      -- use local conservation to rewrite (2d+carry)%b.
      have : (2 * d + carry) % b =
          2 * d + carry - b * doubleCarryStep b carry d := by omega
      rw [this]
      have hge : b * doubleCarryStep b carry d ≤ 2 * d + carry := by omega
      zify [hge]
      ring
lemma doubleDigitsAux_sum {b : ℕ} (hb : 2 ≤ b) :
    ∀ {ds : List ℕ} {carry : ℕ}, carry ≤ 1 → (∀ d ∈ ds, d < b) →
      (doubleDigitsAux b ds carry).sum + (b - 1) * doubleCarryCountAux b ds carry =
        2 * ds.sum + carry := by
  intro ds
  induction ds with
  | nil => intro carry _ _; simp [doubleDigitsAux, doubleCarryCountAux]
  | cons d ds ih =>
      intro carry hcarry hds
      have hd : d < b := hds d List.mem_cons_self
      have htail : ∀ e ∈ ds, e < b := fun e he => hds e (List.mem_cons_of_mem d he)
      have hnext : doubleCarryStep b carry d ≤ 1 := doubleCarryStep_le_one b carry d
      have hlocal := doubleCarryStep_local hb hcarry hd
      have hih := ih hnext htail
      have hstep := doubleCarryStep_le_one b carry d
      simp only [doubleDigitsAux, doubleCarryCountAux, List.sum_cons]
      -- expand (b-1)*(next + count) and use IH + local conservation
      rw [Nat.mul_add]
      -- both `next` and the mod term are bounded; omega from hlocal, hih.
      have hb1 : 1 ≤ b := by omega
      cases hcs : doubleCarryStep b carry d with
      | zero =>
          simp only [hcs, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at *
          omega
      | succ k =>
          -- next ≤ 1 forces k = 0, i.e. next = 1
          have : k = 0 := by omega
          subst this
          simp only [hcs] at hih ⊢
          -- hlocal: (2d+carry)%b + b*1 = 2d+carry
          have hloc1 : (2 * d + carry) % b + b = 2 * d + carry := by
            simpa [hcs] using hlocal
          omega
theorem digitExcess_eq {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    2 * (Nat.digits b n).sum - (Nat.digits b (2 * n)).sum =
      (b - 1) * doubleCarryCount b (Nat.digits b n) := by
  set ds := Nat.digits b n with hds_def
  set out := doubleDigitsAux b ds 0 with hout_def
  have hdigits : ∀ d ∈ ds, d < b :=
    fun d hd => Nat.digits_lt_base (by omega) hd
  have hout_lt : ∀ x ∈ out, x < b := by
    have := doubleDigitsAux_lt_base hb (ds := ds) (carry := 0) (by omega) hdigits
    simpa [hout_def] using this
  have hout_val : Nat.ofDigits b out = 2 * n := by
    have h := doubleDigitsAux_ofDigits hb (ds := ds) (carry := 0) (by omega) hdigits
    rw [hout_def, h, Nat.add_zero, hds_def, Nat.ofDigits_digits]
  -- digit sum of `2n` equals the sum of the carry-respecting `out` list
  have hout_len : out.length = ds.length + 1 := by
    rw [hout_def]; exact doubleDigitsAux_length b ds 0
  have hout_sum : (Nat.digits b (2 * n)).sum = out.sum := by
    have hmem : out ∈ {L : List ℕ | L.length = out.length ∧ ∀ x ∈ L, x < b} :=
      ⟨rfl, hout_lt⟩
    calc (Nat.digits b (2 * n)).sum
        = (Nat.digits b (Nat.ofDigits b out)).sum := by rw [hout_val]
      _ = out.sum := Nat.sum_digits_ofDigits_eq_sum (by omega) hmem
  have hconserve :
      out.sum + (b - 1) * doubleCarryCountAux b ds 0 = 2 * ds.sum + 0 := by
    have := doubleDigitsAux_sum hb (ds := ds) (carry := 0) (by omega) hdigits
    simpa [hout_def] using this
  rw [hout_sum]
  simp only [doubleCarryCount]
  omega
theorem carryCount_eq_zero_iff {b : ℕ} (_hb : 2 ≤ b) (ds : List ℕ) :
    doubleCarryCountAux b ds 0 = 0 ↔ ∀ d ∈ ds, 2 * d < b := by
  induction ds with
  | nil => simp [doubleCarryCountAux]
  | cons d ds ih =>
      constructor
      · intro h
        -- step at the head used carry-in 0
        have hstep : doubleCarryStep b 0 d = 0 := by
          have : doubleCarryStep b 0 d + doubleCarryCountAux b ds
              (doubleCarryStep b 0 d) = 0 := by
            simpa [doubleCarryCountAux] using h
          omega
        have hhead : 2 * d < b := by
          by_contra hc
          have : doubleCarryStep b 0 d = 1 := by
            unfold doubleCarryStep; simp only [Nat.add_zero]; rw [if_pos (by omega)]
          omega
        -- carry-out is 0, so the tail count (with carry-in 0) is 0 too
        have htail0 : doubleCarryCountAux b ds 0 = 0 := by
          have : doubleCarryCountAux b ds (doubleCarryStep b 0 d) = 0 := by
            have : doubleCarryStep b 0 d + doubleCarryCountAux b ds
                (doubleCarryStep b 0 d) = 0 := by
              simpa [doubleCarryCountAux] using h
            omega
          rwa [hstep] at this
        simp_all
      · intro h
        have hhead : 2 * d < b := h d List.mem_cons_self
        have htail : ∀ e ∈ ds, 2 * e < b := fun e he => h e (List.mem_cons_of_mem d he)
        have hstep : doubleCarryStep b 0 d = 0 := by
          unfold doubleCarryStep; simp only [Nat.add_zero]; rw [if_neg (by omega)]
        simpa only [doubleCarryCountAux, hstep, Nat.zero_add] using ih.mpr htail
theorem coprime_centralBinom_prime_iff {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    Nat.Coprime (Nat.centralBinom n) p ↔ LowDoubleDigits p n := by
  have hpprime : Nat.Prime p := hp.out
  have hp2 : 2 ≤ p := hpprime.two_le
  -- Kummer valuation identity, then carry-count translation.
  have hform := Egrs75.ConcreteMath.sub_one_mul_padicValNat_centralBinom p n
  have hexcess := digitExcess_eq hp2 n
  -- (p-1)·ν = (p-1)·carryCount  ⇒  ν = carryCount.
  have hval_eq : padicValNat p (Nat.centralBinom n) =
      doubleCarryCount p (Nat.digits p n) := by
    have hp1pos : 0 < p - 1 := by omega
    have : (p - 1) * padicValNat p (Nat.centralBinom n) =
        (p - 1) * doubleCarryCount p (Nat.digits p n) := by
      rw [hform, hexcess]
    exact Nat.eq_of_mul_eq_mul_left hp1pos this
  -- coprime ⇔ ¬ p ∣ C ⇔ ν = 0 ⇔ carryCount = 0 ⇔ LowDoubleDigits.
  have hcop : Nat.Coprime (Nat.centralBinom n) p ↔ ¬ p ∣ Nat.centralBinom n := by
    rw [Nat.coprime_comm]; exact hpprime.coprime_iff_not_dvd
  have hdvd : p ∣ Nat.centralBinom n ↔ padicValNat p (Nat.centralBinom n) ≠ 0 :=
    dvd_iff_padicValNat_ne_zero (Nat.centralBinom_ne_zero n)
  rw [hcop, hdvd, not_not, hval_eq, doubleCarryCount]
  exact carryCount_eq_zero_iff hp2 (Nat.digits p n)
theorem centralBinom_coprime_105_iff (n : ℕ) :
    Nat.Coprime (Nat.centralBinom n) 105 ↔
      LowDoubleDigits 3 n ∧ LowDoubleDigits 5 n ∧ LowDoubleDigits 7 n := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h105 : (105 : ℕ) = 3 * (5 * 7) := by norm_num
  rw [h105, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right,
    coprime_centralBinom_prime_iff (p := 3),
    coprime_centralBinom_prime_iff (p := 5),
    coprime_centralBinom_prime_iff (p := 7)]
example : Nat.Coprime (Nat.centralBinom 10) 105 := by
  rw [centralBinom_coprime_105_iff]
  unfold LowDoubleDigits
  refine ⟨?_, ?_, ?_⟩ <;> decide
example : ¬ Nat.Coprime (Nat.centralBinom 2) 105 := by
  rw [centralBinom_coprime_105_iff]
  intro h
  have := h.1 2 (by decide)
  omega
end Egrs75.Erdos376


