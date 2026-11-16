-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerSeriesFinite
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerSeriesFinite
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:53:37.892199+00:00
-- url     : https://prove2.me/theorems/65fb77eb-b5a3-489c-88a5-2d2a2211124a
-- title:
--   Computable analysis · EulerSeriesFinite · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerSeriesFinite.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerFinite
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-! Finite binomial/factorial comparison. The falling-factorial argument is
extracted independently of the legacy exponential analytic certificates. -/
namespace ComputableAnalysis.EulerSeriesFinite
open EulerFinite RationalMajorant
set_option maxHeartbeats 2000000

def fallingFactorialRat (M : Rat) : Nat -> Rat
  | 0 => 1
  | k + 1 => fallingFactorialRat M k * (M - (k : Rat))

private theorem fallingFactorialRat_succ (M : Rat) (k : Nat) :
    fallingFactorialRat M (k + 1) =
      fallingFactorialRat M k * (M - (k : Rat)) :=
  rfl

/-- The falling-factorial form of Pascal's identity. This is a finite
rational polynomial identity, not an analytic use of the binomial theorem. -/
private theorem fallingFactorialRat_pascal_succ (M : Rat) (k : Nat) :
    fallingFactorialRat (M + 1) (k + 1) =
      fallingFactorialRat M (k + 1) +
        ((k + 1 : Nat) : Rat) * fallingFactorialRat M k := by
  induction k with
  | zero =>
      simp [fallingFactorialRat, Rat.sub_eq_add_neg]
      grind [Rat.sub_eq_add_neg]
  | succ k ih =>
      rw [fallingFactorialRat_succ (M + 1) (k + 1),
        fallingFactorialRat_succ M (k + 1), ih,
        fallingFactorialRat_succ M k]
      have hcast1 : (((k + 1 : Nat) : Rat)) = (k : Rat) + 1 := by
        exact_mod_cast (by omega : k + 1 = k + 1)
      have hcast2 : (((k + 2 : Nat) : Rat)) = (k : Rat) + 2 := by
        exact_mod_cast (by omega : k + 2 = k + 2)
      rw [hcast1, hcast2]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.add_assoc, Rat.add_comm, Rat.mul_comm]

/-- The `k`th term of the finite binomial expansion of `(1 + x)^M` when the
exponent `M` is a natural number embedded in the rationals. -/
def eulerBinomialTerm (M x : Rat) (k : Nat) : Rat :=
  fallingFactorialRat M k / factorialRat k * x ^ k

 /-- A finite prefix of the rational binomial expansion.  At the natural
endpoint `M = m`, the prefix of `m + 1` terms is exactly `(1 + x)^m`. -/
def eulerBinomialPrefix (M x : Rat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      eulerBinomialPrefix M x count + eulerBinomialTerm M x count

private theorem eulerBinomialTerm_zero (M x : Rat) :
    eulerBinomialTerm M x 0 = 1 := by
  unfold eulerBinomialTerm fallingFactorialRat factorialRat factorial
  grind [Rat.div_def]

/-- The coefficient identity needed to expand one more finite Euler
factor.  The factorial denominator cancels entirely by rational algebra. -/
private theorem eulerBinomialTerm_pascal_succ (M x : Rat) (k : Nat) :
    eulerBinomialTerm (M + 1) x (k + 1) =
      eulerBinomialTerm M x (k + 1) + x * eulerBinomialTerm M x k := by
  unfold eulerBinomialTerm
  rw [fallingFactorialRat_pascal_succ, FormalPowerSeries.factorialRat_succ,
    Rat.pow_succ, Rat.div_def, Rat.div_def, Rat.div_def]
  have hkpos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by
    exact_mod_cast Nat.succ_pos k
  have hfactpos : (0 : Rat) < factorialRat k :=
    RationalMajorant.factorialRat_pos k
  have hkne : ((k + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hkpos
  have hfactne : factorialRat k ≠ 0 := Rat.ne_of_gt hfactpos
  rw [Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.mul_inv_cancel]

private theorem eulerBinomialPrefix_succ (M x : Rat) (count : Nat) :
    eulerBinomialPrefix M x (count + 1) =
      eulerBinomialPrefix M x count + eulerBinomialTerm M x count :=
  rfl

/-- Summing Pascal's identity over a finite prefix. -/
private theorem eulerBinomialPrefix_pascal (M x : Rat) (count : Nat) :
    eulerBinomialPrefix (M + 1) x (count + 1) =
      eulerBinomialPrefix M x (count + 1) +
        x * eulerBinomialPrefix M x count := by
  induction count with
  | zero =>
      grind [eulerBinomialPrefix, eulerBinomialTerm_zero]
  | succ count ih =>
      calc
        eulerBinomialPrefix (M + 1) x ((count + 1) + 1) =
            eulerBinomialPrefix (M + 1) x (count + 1) +
              eulerBinomialTerm (M + 1) x (count + 1) := rfl
        _ = (eulerBinomialPrefix M x (count + 1) +
              x * eulerBinomialPrefix M x count) +
            (eulerBinomialTerm M x (count + 1) +
              x * eulerBinomialTerm M x count) := by
              rw [ih, eulerBinomialTerm_pascal_succ]
        _ = (eulerBinomialPrefix M x (count + 1) +
              eulerBinomialTerm M x (count + 1)) +
            x * eulerBinomialPrefix M x (count + 1) := by
              rw [eulerBinomialPrefix_succ M x count]
              grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.mul_assoc,
                Rat.mul_comm]
        _ = eulerBinomialPrefix M x ((count + 1) + 1) +
            x * eulerBinomialPrefix M x (count + 1) := rfl

private theorem fallingFactorialRat_nat_succ_zero (m : Nat) :
    fallingFactorialRat (m : Rat) (m + 1) = 0 := by
  rw [fallingFactorialRat_succ]
  have hcast : ((m : Nat) : Rat) = (m : Rat) := rfl
  rw [hcast]
  grind [Rat.sub_eq_add_neg]

private theorem eulerBinomialTerm_nat_succ_zero (m : Nat) (x : Rat) :
    eulerBinomialTerm (m : Rat) x (m + 1) = 0 := by
  unfold eulerBinomialTerm
  rw [fallingFactorialRat_nat_succ_zero]
  grind [Rat.div_def]

/-- The finite binomial expansion used to compare the Euler powers with
factorial-series prefixes. -/
theorem euler_binomial_prefix_nat_expansion (m : Nat) (x : Rat) :
    eulerBinomialPrefix (m : Rat) x (m + 1) = (1 + x) ^ m := by
  induction m with
  | zero =>
      grind [eulerBinomialPrefix, eulerBinomialTerm_zero]
  | succ m ih =>
      have hcast : (((m + 1 : Nat) : Rat)) = (m : Rat) + 1 := by
        exact_mod_cast (by omega : m + 1 = m + 1)
      rw [hcast, eulerBinomialPrefix_pascal, eulerBinomialPrefix_succ,
        eulerBinomialTerm_nat_succ_zero, ih, Rat.pow_succ]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.mul_assoc,
        Rat.mul_comm]


def term (q : Rat) (k : Nat) : Rat := q^k/factorialRat k

def factorialPrefix (q : Rat) : Nat → Rat
  | 0 => 0
  | k+1 => factorialPrefix q k+term q k

def correction (N : Nat) : Nat → Rat
  | 0 => 1
  | k+1 => correction N k*(1-(k:Rat)/(N:Rat))

theorem correction_bounds {N k : Nat} (hN : 0<N) (hk : k≤N+1) :
    0≤correction N k ∧ correction N k≤1 ∧
      1-correction N k≤(k:Rat)*((k:Rat)-1)/(N:Rat) := by
  have hNr : 0<(N:Rat) := Rat.natCast_pos.mpr hN
  have hi := Rat.inv_pos.mpr hNr
  have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hNr)
  induction k with
  | zero =>
    change (0:Rat)≤1 ∧ 1≤1 ∧ 1-1≤0*(0-1)/(N:Rat)
    constructor; decide +kernel
    constructor; decide +kernel
    grind [Rat.div_def]
  | succ k ih =>
    obtain ⟨hlo,hhi,he⟩ := ih (by omega)
    have hkN : (k:Rat)≤(N:Rat) := by exact_mod_cast (show k≤N by omega)
    have hk0 : (0:Rat)≤(k:Rat) := Rat.natCast_nonneg
    have hstep := Rat.mul_le_mul_of_nonneg_right hkN (Rat.le_of_lt hi)
    have ht : 0≤(k:Rat)/(N:Rat) := Rat.mul_nonneg hk0 (Rat.le_of_lt hi)
    have hp := Rat.mul_nonneg hlo (show 0≤1-(k:Rat)/(N:Rat) by grind [Rat.div_def])
    have hdec := Rat.mul_nonneg hlo ht
    have hcor := Rat.mul_le_mul_of_nonneg_right hhi ht
    rw [correction]
    have hcast : ((k+1:Nat):Rat)=(k:Rat)+1 := by rw [Rat.natCast_add]; rfl
    rw [hcast]
    exact ⟨hp,by grind only,by grind only [Rat.div_def]⟩

theorem correction_as_falling {N : Nat} (hN : 0<N) (k : Nat) :
    correction N k=fallingFactorialRat (N:Rat) k*((N:Rat)⁻¹)^k := by
  have hc := Rat.mul_inv_cancel (N:Rat) (by exact_mod_cast (Nat.ne_of_gt hN))
  induction k with
  | zero => simp only [correction,fallingFactorialRat,Rat.pow_zero,Rat.mul_one]
  | succ k ih =>
    rw [correction,fallingFactorialRat_succ,Rat.pow_succ,ih]
    grind only [Rat.div_def]

theorem binomial_term_eq {N : Nat} (hN : 0<N) (q : Rat) (k : Nat) :
    eulerBinomialTerm (N:Rat) (q/(N:Rat)) k=term q k*correction N k := by
  rw [correction_as_falling hN]
  simp only [eulerBinomialTerm,term,Rat.div_def,mul_pow]
  grind only

theorem term_abs (q : Rat) (k : Nat) : qabs (term q k)=factorialTailTerm (qabs q) k := by
  simp only [term,factorialTailTerm,Rat.div_def,qabs_mul,qabs_pow_eq_pow_qabs]
  rw [qabs_eq_self_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr (factorialRat_pos k)))]

theorem weight_nonnegative (k : Nat) : 0≤(k:Rat)*((k:Rat)-1) := by
  by_cases hk : k=0
  · subst k; decide +kernel
  have h : (1:Rat)≤(k:Rat) := by exact_mod_cast (show 1≤k by omega)
  exact Rat.mul_nonneg Rat.natCast_nonneg (by grind only)

theorem term_error {N k : Nat} (hN : 0<N) (hk : k≤N+1) {q C : Rat}
    (hC : 0≤C) (hq : qabs q≤C) :
    qabs (term q k-eulerBinomialTerm (N:Rat) (q/(N:Rat)) k)≤
      factorialTailTerm C k*(k:Rat)*((k:Rat)-1)/(N:Rat) := by
  obtain ⟨hc0,hc1,herr⟩ := correction_bounds hN hk
  have hw := weight_nonnegative k
  have ht := factorialTailTerm_nonneg hC k
  have hcoef : qabs (term q k)≤factorialTailTerm C k := by
    rw [term_abs]
    exact factorialTailTerm_mono (qabs_nonneg q) hq k
  have hcorr : 0≤1-correction N k := by grind only
  have h1 := Rat.mul_le_mul_of_nonneg_right hcoef hcorr
  have h2 := Rat.mul_le_mul_of_nonneg_left herr ht
  rw [binomial_term_eq hN]
  have he : term q k-term q k*correction N k=term q k*(1-correction N k) := by grind only
  rw [he,qabs_mul,qabs_eq_self_of_nonneg hcorr]
  grind only [Rat.div_def]

def weighted (C : Rat) : Nat → Rat
  | 0 => 0
  | k+1 => weighted C k+factorialTailTerm C k*(k:Rat)*((k:Rat)-1)

theorem prefix_error {N k : Nat} (hN : 0<N) (hk : k≤N+1) {q C : Rat}
    (hC : 0≤C) (hq : qabs q≤C) :
    qabs (factorialPrefix q k-eulerBinomialPrefix (N:Rat) (q/(N:Rat)) k)≤weighted C k/(N:Rat) := by
  induction k with
  | zero => change qabs (0-0)≤0/(N:Rat); simp only [Rat.sub_self]; grind [Rat.div_def,qabs]
  | succ k ih =>
    have H := ih (by omega)
    have K := term_error hN (by omega : k≤N+1) hC hq
    have Hsum := Rat.le_trans (qabs_add_le
      (factorialPrefix q k-eulerBinomialPrefix (N:Rat) (q/(N:Rat)) k)
      (term q k-eulerBinomialTerm (N:Rat) (q/(N:Rat)) k)) (rat_add_le_add H K)
    have he : factorialPrefix q (k+1)-eulerBinomialPrefix (N:Rat) (q/(N:Rat)) (k+1)=
      (factorialPrefix q k-eulerBinomialPrefix (N:Rat) (q/(N:Rat)) k)+
      (term q k-eulerBinomialTerm (N:Rat) (q/(N:Rat)) k) := by
      rw [factorialPrefix,eulerBinomialPrefix]; grind only
    rw [he]
    exact Rat.le_trans Hsum (by dsimp [weighted]; grind only [Rat.div_def])

theorem weight_shift (C : Rat) (k : Nat) :
    factorialTailTerm C (k+2)*((k+2:Nat):Rat)*(((k+2:Nat):Rat)-1)=C*C*factorialTailTerm C k := by
  have h1 : ((k+1:Nat):Rat)=(k:Rat)+1 := by rw [Rat.natCast_add]; rfl
  have h2 : ((k+2:Nat):Rat)=(k:Rat)+2 := by rw [Rat.natCast_add]; rfl
  have hc1 := Rat.mul_inv_cancel ((k+1:Nat):Rat) (by exact_mod_cast Nat.succ_ne_zero k)
  have hc2 := Rat.mul_inv_cancel ((k+2:Nat):Rat) (by exact_mod_cast (show k+2≠0 by omega))
  rw [show k+2=(k+1)+1 by omega,factorialTailTerm_succ,factorialTailTerm_succ]
  rw [h1] at hc1
  rw [h2] at hc2
  have h2x : ((k+1+1:Nat):Rat)=(k:Rat)+2 := by simpa only [Nat.add_assoc] using h2
  rw [h1,h2x]
  grind only [Rat.div_def]

theorem weighted_shift (C : Rat) (k : Nat) :
    weighted C (k+2)=C*C*factorialTailPartial C 0 k := by
  induction k with
  | zero =>
    change weighted C 2=C*C*0
    simp only [weighted]
    change 0+factorialTailTerm C 0*0*(0-1)+factorialTailTerm C 1*1*(1-1)=C*C*0
    grind only
  | succ k ih =>
    rw [show (k+1)+2=(k+2)+1 by omega,weighted,weight_shift,ih,factorialTailPartial]
    rw [Nat.zero_add]
    grind only

theorem weighted_bound {C : Rat} (hC : 0≤C) (k : Nat) :
    weighted C k≤C*C*factorialSeriesFiniteBound C := by
  have hsq := Rat.mul_nonneg hC hC
  have hB := factorialSeriesFiniteBound_nonneg hC
  by_cases hk : 2≤k
  · rw [show k=(k-2)+2 by omega,weighted_shift]
    exact Rat.mul_le_mul_of_nonneg_left (factorialTailPartial_zero_le_finiteBound hC _) hsq
  · have hz : k=0 ∨ k=1 := by omega
    have H := Rat.mul_nonneg hsq hB
    rcases hz with rfl | rfl
    · exact H
    · change 0+factorialTailTerm C 0*0*(0-1)≤_
      grind only

/-- The entire binomial product differs from the same-length factorial
prefix by an explicit error tending to zero with the Euler step count. -/
theorem euler_factorial_error {N : Nat} (hN : 0<N) {q C : Rat}
    (hC : 0≤C) (hq : qabs q≤C) :
    qabs (factorialPrefix q (N+1)-lower q N)≤C*C*factorialSeriesFiniteBound C/(N:Rat) := by
  have H := prefix_error hN (Nat.le_refl (N+1)) hC hq
  rw [euler_binomial_prefix_nat_expansion] at H
  have W := Rat.mul_le_mul_of_nonneg_right (weighted_bound hC (N+1))
    (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hN)))
  exact Rat.le_trans H W

end ComputableAnalysis.EulerSeriesFinite


