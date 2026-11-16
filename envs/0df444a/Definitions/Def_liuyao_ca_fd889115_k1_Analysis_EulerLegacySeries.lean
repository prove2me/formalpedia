-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerLegacySeries
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerLegacySeries
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:11:06.062319+00:00
-- url     : https://prove2.me/theorems/55cba6ab-1a8a-4607-8fc2-98c961c214c4
-- title:
--   Computable analysis · EulerLegacySeries · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerLegacySeries.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerSeriesIdentity
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Exp

set_option autoImplicit true

/-! Exact comparison with the existing adaptive factorial-tail evaluator.
Only its finite loop is used; no legacy analytic certificate is assumed. -/
namespace ComputableAnalysis.EulerLegacySeries
open EulerSeriesFinite EulerSeriesIdentity EulerPowerLimit EulerReal
open RationalMajorant ComputableCoefficient RealApproximationOrder RawLimit
set_option maxHeartbeats 2500000

private def powerSeriesLoopStep (x : Rat) (s : Rat × Rat)
    (k : Nat) : Rat × Rat :=
  (s.1 + s.2, s.2 * x / ((k : Rat) + 1))

private def powerSeriesLoopPairFrom (x : Rat) (xs : List Nat)
    (sum term : Rat) : Rat × Rat :=
  Id.run do
    let mut sum : Rat := sum
    let mut term : Rat := term
    for k in xs do
      sum := sum + term
      term := term * x / ((k + 1 : Nat) : Rat)
    return (sum, term)

private def powerSeriesLoopPair (x : Rat) (xs : List Nat) :
    Rat × Rat :=
  powerSeriesLoopPairFrom x xs 0 1

private theorem powerSeriesLoopPairFrom_eq_foldl
    (x : Rat) (xs : List Nat) (sum term : Rat) :
    powerSeriesLoopPairFrom x xs sum term =
      xs.foldl (powerSeriesLoopStep x) (sum, term) := by
  induction xs generalizing sum term with
  | nil => rfl
  | cons k ks ih =>
      calc
        powerSeriesLoopPairFrom x (k :: ks) sum term =
            powerSeriesLoopPairFrom x ks
              (sum + term) (term * x / ((k : Rat) + 1)) := by
          simp [powerSeriesLoopPairFrom]
        _ = ks.foldl (powerSeriesLoopStep x)
            (sum + term, term * x / ((k : Rat) + 1)) := by
          exact ih (sum + term) (term * x / ((k : Rat) + 1))
        _ = (k :: ks).foldl (powerSeriesLoopStep x) (sum, term) := by
          rfl

private theorem powerSeriesLoopPair_eq_foldl
    (x : Rat) (xs : List Nat) :
    powerSeriesLoopPair x xs =
      xs.foldl (powerSeriesLoopStep x) (0, 1) := by
  unfold powerSeriesLoopPair
  exact powerSeriesLoopPairFrom_eq_foldl x xs 0 1

private def powerSeriesState (x : Rat) (N : Nat) : Rat × Rat :=
  (List.range N).foldl (powerSeriesLoopStep x) (0, 1)

private theorem powerSeriesState_succ (x : Rat) (N : Nat) :
    powerSeriesState x (N + 1) =
      powerSeriesLoopStep x (powerSeriesState x N) N := by
  unfold powerSeriesState
  rw [List.range_succ, List.foldl_append]
  rfl


theorem term_succ (q : Rat) (k : Nat) : term q (k+1)=term q k*q/((k+1:Nat):Rat) := by
  simp only [term,FormalPowerSeries.factorialRat_succ,Rat.pow_succ,Rat.div_def,Rat.inv_mul_rev]
  grind only

theorem state_term (q : Rat) (k : Nat) : (powerSeriesState q k).2=term q k := by
  induction k with
  | zero => change 1=q^0/factorialRat 0; simp only [Rat.pow_zero,factorialRat,factorial]; decide +kernel
  | succ k ih =>
    rw [powerSeriesState_succ]
    simp only [powerSeriesLoopStep,term_succ,ih]
    congr 1
    rw [Rat.natCast_add]
    rfl

theorem state_center (q : Rat) (k : Nat) : (powerSeriesState q k).1=factorialPrefix q k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powerSeriesState_succ]; simp only [powerSeriesLoopStep,ih,state_term,factorialPrefix]

theorem adaptive_compute (q : Rat) (n : Nat) :
    (expPowerSeries q).compute n=
      {lo := factorialPrefix q (expPowerSeriesTerms q n)-
        qabs (term q (expPowerSeriesTerms q n))/(1-expPowerSeriesTailRatioBound q n),
       hi := factorialPrefix q (expPowerSeriesTerms q n)+
        qabs (term q (expPowerSeriesTerms q n))/(1-expPowerSeriesTailRatioBound q n)} := by
  have H : expPowerSeriesPartialAndTailBound q n=
      ((powerSeriesState q (expPowerSeriesTerms q n)).1,
        qabs (powerSeriesState q (expPowerSeriesTerms q n)).2/(1-expPowerSeriesTailRatioBound q n)) := by
    change ((powerSeriesLoopPair q (List.range (expPowerSeriesTerms q n))).1,
      qabs (powerSeriesLoopPair q (List.range (expPowerSeriesTerms q n))).2/(1-expPowerSeriesTailRatioBound q n))=_
    rw [powerSeriesLoopPair_eq_foldl]
    rfl
  simp only [expPowerSeries,H,state_center,state_term]

theorem ratio_properties (q : Rat) (n : Nat) :
    0≤expPowerSeriesTailRatioBound q n ∧ expPowerSeriesTailRatioBound q n≤1/2 := by
  have HQ := qabs_le_numNatAbs_succ q
  have HT : 2*(q.num.natAbs+1)≤expPowerSeriesTerms q n+1 := by unfold expPowerSeriesTerms; omega
  have HTr : 2*((q.num.natAbs+1:Nat):Rat)≤((expPowerSeriesTerms q n+1:Nat):Rat) := by exact_mod_cast HT
  have HD : 0<((expPowerSeriesTerms q n+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos _)
  have HI := Rat.inv_pos.mpr HD
  have HC := Rat.mul_inv_cancel ((expPowerSeriesTerms q n+1:Nat):Rat) (Rat.ne_of_gt HD)
  have H := Rat.mul_le_mul_of_nonneg_right HTr (Rat.le_of_lt HI)
  have Hq := Rat.mul_le_mul_of_nonneg_right HQ (Rat.le_of_lt HI)
  exact ⟨Rat.mul_nonneg (qabs_nonneg q) (Rat.le_of_lt HI),by dsimp [expPowerSeriesTailRatioBound]; grind only [Rat.div_def]⟩

def center (q : Rat) (n : Nat) : Rat := factorialPrefix q (expPowerSeriesTerms q n)
def radius (q : Rat) (n : Nat) : Rat :=
  qabs (term q (expPowerSeriesTerms q n))/(1-expPowerSeriesTailRatioBound q n)

theorem compute_eq (q : Rat) (n : Nat) :
    (expPowerSeries q).compute n={lo := center q n-radius q n,hi := center q n+radius q n} := adaptive_compute q n

theorem radius_nonnegative (q : Rat) (n : Nat) : 0≤radius q n := by
  have H := (ratio_properties q n).2
  exact Rat.mul_nonneg (qabs_nonneg _) (Rat.le_of_lt (Rat.inv_pos.mpr (by grind only)))

theorem terms_succ (q : Rat) (n : Nat) : expPowerSeriesTerms q (n+1)=expPowerSeriesTerms q n+1 := by
  unfold expPowerSeriesTerms; omega

theorem ratio_antitone (q : Rat) (n : Nat) :
    expPowerSeriesTailRatioBound q (n+1)≤expPowerSeriesTailRatioBound q n := by
  unfold expPowerSeriesTailRatioBound
  rw [terms_succ]
  apply Rat.mul_le_mul_of_nonneg_left _ (qabs_nonneg q)
  apply EulerFinite.inv_antitone
  · exact Rat.natCast_pos.mpr (Nat.succ_pos _)
  · exact_mod_cast (show expPowerSeriesTerms q n+1≤expPowerSeriesTerms q n+1+1 by omega)

theorem abs_term_succ (q : Rat) (k : Nat) :
    qabs (term q (k+1))=qabs (term q k)*(qabs q/((k+1:Nat):Rat)) := by
  rw [term_succ,Rat.div_def,qabs_mul,qabs_mul]
  rw [qabs_eq_self_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.succ_pos k))))]
  grind only [Rat.div_def]

theorem radius_step (q : Rat) (n : Nat) :
    radius q (n+1)+qabs (term q (expPowerSeriesTerms q n))≤radius q n := by
  have HR := ratio_antitone q n
  have ⟨hr0,hr⟩ := ratio_properties q n
  have hs := (ratio_properties q (n+1)).2
  have HD : 0<1-expPowerSeriesTailRatioBound q n := by grind only
  have HD' : 0<1-expPowerSeriesTailRatioBound q (n+1) := by grind only
  have HI := EulerFinite.inv_antitone HD (by grind only :
    1-expPowerSeriesTailRatioBound q n≤1-expPowerSeriesTailRatioBound q (n+1))
  have HA := qabs_nonneg (term q (expPowerSeriesTerms q n))
  have HP := Rat.mul_nonneg HA hr0
  have H := Rat.mul_le_mul_of_nonneg_left HI HP
  have HC := Rat.mul_inv_cancel (1-expPowerSeriesTailRatioBound q n) (Rat.ne_of_gt HD)
  have HCscaled := congrArg (fun v : Rat => qabs (term q (expPowerSeriesTerms q n))*v) HC
  unfold radius
  rw [terms_succ,abs_term_succ]
  change qabs (term q (expPowerSeriesTerms q n))*expPowerSeriesTailRatioBound q n/
    (1-expPowerSeriesTailRatioBound q (n+1))+qabs (term q (expPowerSeriesTerms q n))≤_
  grind only [Rat.div_def]

theorem adaptive_nested (q : Rat) {n m : Nat} (hnm : n≤m) :
    ((expPowerSeries q).compute n).lo≤((expPowerSeries q).compute m).lo ∧
    ((expPowerSeries q).compute m).hi≤((expPowerSeries q).compute n).hi := by
  induction hnm with
  | refl => exact ⟨Rat.le_refl,Rat.le_refl⟩
  | @step m hnm ih =>
    have H := radius_step q m
    have HL := neg_qabs_le_self (term q (expPowerSeriesTerms q m))
    have HU := self_le_qabs (term q (expPowerSeriesTerms q m))
    have HC : center q (m+1)=center q m+term q (expPowerSeriesTerms q m) := by
      unfold center; rw [terms_succ,factorialPrefix]
    rw [compute_eq q n,compute_eq q m] at ih
    rw [compute_eq q n,compute_eq q (m+1)]
    simp only at ih ⊢
    constructor <;> grind only

theorem abs_stage_geometric (q : Rat) (n : Nat) :
    qabs (term q (expPowerSeriesTerms q n))≤qabs (term q (expPowerSeriesTerms q 0))*((1:Rat)/2)^n := by
  induction n with
  | zero => simp only [Rat.pow_zero,Rat.mul_one,Rat.le_refl]
  | succ n ih =>
    rw [terms_succ,abs_term_succ]
    have H := Rat.mul_le_mul_of_nonneg_left (ratio_properties q n).2 (qabs_nonneg (term q (expPowerSeriesTerms q n)))
    have H' := Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel : (0:Rat)≤1/2)
    rw [Rat.pow_succ]
    exact Rat.le_trans H (by grind only)

theorem radius_le_twice (q : Rat) (n : Nat) :
    radius q n≤2*qabs (term q (expPowerSeriesTerms q n)) := by
  have HR := (ratio_properties q n).2
  have HD : 0<1-expPowerSeriesTailRatioBound q n := by grind only
  have H := EulerFinite.inv_antitone (by decide +kernel : (0:Rat)<1/2)
    (show (1:Rat)/2≤1-expPowerSeriesTailRatioBound q n by grind only)
  have H' := Rat.mul_le_mul_of_nonneg_left H (qabs_nonneg (term q (expPowerSeriesTerms q n)))
  change qabs (term q (expPowerSeriesTerms q n))*(1-expPowerSeriesTailRatioBound q n)⁻¹≤_
  have Htwo : ((1:Rat)/2)⁻¹=2 := by decide +kernel
  rw [Htwo] at H'
  grind only

/-- Kernel-checked validity for the original adaptive series evaluator,
independent of the older native-decision analytic certificate. -/
theorem adaptive_valid (q : Rat) : (expPowerSeries q).Valid := by
  have ordered (n : Nat) : ((expPowerSeries q).compute n).lo≤((expPowerSeries q).compute n).hi := by
    rw [compute_eq]; simp only; have H := radius_nonnegative q n; grind only
  refine ⟨?_,?_,?_⟩
  · intro n; change 0≤_ - _; have H := ordered n; grind only
  · intro n m hnm
    have H := adaptive_nested q hnm
    exact ⟨H.1,ordered m,H.2⟩
  · apply shrinksToZero_of_ratOverSuccBound (C := 4*qabs (term q (expPowerSeriesTerms q 0)))
    intro n
    have H := radius_le_twice q n
    have G := abs_stage_geometric q n
    have T := Rat.mul_le_mul_of_nonneg_left (half_pow_le_one_div_succ n)
      (qabs_nonneg (term q (expPowerSeriesTerms q 0)))
    rw [compute_eq]
    unfold QInterval.width
    dsimp only
    grind only [Rat.div_def]

theorem finite_rational (q : Rat) (k : Nat) :
    (finiteValue (parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q)) k).real.preferred.Equiv
      (RealCompute.ofRat (factorialPrefix q k)) := by
  apply Value.equiv_of_samples _ (Value.rational (factorialPrefix q k)) 0
  intro m hm s hs
  have HQ := hs (RealCompute.Certified.ofRaw (RealCompute.ofRat q) (RealCompute.ofRat_valid q))
  change q≤(parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).sample s ∧
    (parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).sample s≤q at HQ
  have H : (parameter (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).sample s=q := Rat.le_antisymm HQ.2 HQ.1
  simp only [partial_sample,H,Value.rational]

theorem prefixes_tend_to_euler (q : Rat) :
    TendsTo (fun k => RealCompute.ofRat (factorialPrefix q k)) (sample q) :=
  congr_sequence (exponential_hasSum (x := RealCompute.ofRat q) (RealCompute.ofRat_valid q)) (fun _ => RealCompute.ofRat_valid _)
    (finite_rational q)

/-- A limit of values eventually in a closed rational interval is in that
interval. This uses only the existing represented limit and exact order. -/
theorem limit_in_interval {u : Nat → RealCompute} {x : RealCompute} (h : TendsTo u x) (I : QInterval)
    (hb : ∃ N, ∀ n, N≤n → InInterval (u n) I) : InInterval x I := by
  obtain ⟨K,hK⟩ := hb
  constructor
  · intro i j
    by_cases H : I.lo≤(x.compute j).hi
    · exact H
    have HP : 0<(I.lo-(x.compute j).hi)/2 := by grind only
    obtain ⟨N,hN⟩ := h.2.2 j ⟨_,HP⟩
    let n := max N K
    have HU := RealCompute.le_trans (h.2.1 n) (hK n (by dsimp [n]; omega)).1 (hN n (by dsimp [n]; omega)).2 0 0
    change I.lo≤(x.compute j).hi+(I.lo-(x.compute j).hi)/2 at HU
    grind only
  · intro i j
    by_cases H : (x.compute i).lo≤I.hi
    · exact H
    have HP : 0<((x.compute i).lo-I.hi)/2 := by grind only
    obtain ⟨N,hN⟩ := h.2.2 i ⟨_,HP⟩
    let n := max N K
    have HL := RealCompute.le_trans (h.2.1 n) (hN n (by dsimp [n]; omega)).1 (hK n (by dsimp [n]; omega)).2 0 0
    change (x.compute i).lo-((x.compute i).lo-I.hi)/2≤I.hi at HL
    grind only

theorem adaptive_contains_euler (q : Rat) (i : Nat) :
    InInterval (sample q) ((expPowerSeries q).compute i) := by
  apply limit_in_interval (prefixes_tend_to_euler q)
  refine ⟨expPowerSeriesTerms q i,fun k hk => ?_⟩
  let j := k-expPowerSeriesTerms q 0
  have Hterms : expPowerSeriesTerms q j=k := by dsimp [j,expPowerSeriesTerms] at *; omega
  have Hij : i≤j := by dsimp [j,expPowerSeriesTerms] at *; omega
  have HN := adaptive_nested q Hij
  have HR := radius_nonnegative q j
  rw [compute_eq q j] at HN
  have HC : center q j=factorialPrefix q k := by unfold center; rw [Hterms]
  rw [HC] at HN
  change ((expPowerSeries q).compute i).lo≤factorialPrefix q k-radius q j ∧
    factorialPrefix q k+radius q j≤((expPowerSeries q).compute i).hi at HN
  constructor
  · intro n m
    change ((expPowerSeries q).compute i).lo≤factorialPrefix q k
    grind only
  · intro n m
    change factorialPrefix q k≤((expPowerSeries q).compute i).hi
    grind only

/-- The original adaptive power-series program agrees with the ODE Euler
program at every rational input, with both actual programs proved valid. -/
theorem adaptive_equiv_euler (q : Rat) : (expPowerSeries q).Equiv (sample q) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  have H := adaptive_contains_euler q n
  exact ⟨H.1 0 n,H.2 n 0⟩

/-- The represented factorial-prefix extension is an extension of the
existing primary rational power-series sampler. -/
theorem seriesAt_rational (q : Rat) :
    (seriesAt (RealCompute.ofRat q) (RealCompute.ofRat_valid q)).Equiv (expPowerSeries q) :=
  RealCompute.equiv_trans (seriesAt_valid (x := RealCompute.ofRat q) (RealCompute.ofRat_valid q)) (sample_valid q) (adaptive_valid q)
    (seriesAt_equiv_euler (x := RealCompute.ofRat q) (RealCompute.ofRat_valid q)) (RealCompute.equiv_symm (adaptive_equiv_euler q))

/-- The old display wrapper is not a valid general exponential name. This
counterexample is why the full power-limit theorem uses justified errors. -/
theorem legacy_euler_candidate_not_valid : ¬(expEuler 2).Valid := by
  intro H
  have HS := (H.2.1 0 1 (by decide)).2.2
  have HB : ¬((expEuler 2).compute 1).hi≤((expEuler 2).compute 0).hi := by decide +kernel
  exact HB HS

end ComputableAnalysis.EulerLegacySeries


