-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerTaylorFTC
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerTaylorFTC
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:15:16.722392+00:00
-- url     : https://prove2.me/theorems/7745800c-2a7b-4335-93fc-30ff29b7a53b
-- title:
--   Computable analysis · EulerTaylorFTC · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerTaylorFTC.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCFromSupportingSlopes
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerRealDerivative
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RepeatedFTC
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerSeriesIdentity

set_option autoImplicit true

/-! Repeated FTC for the Euler ODE exponential. The derivative and finite
order estimates below precede the factorial series. -/
namespace ComputableAnalysis.EulerTaylorFTC
open ComputableCoefficient RealApproximationOrder FTCRealOrder FTCRealCalculus
set_option maxHeartbeats 600000

def value (t : Rat) : Value := parameter (EulerReal.sample t) (EulerReal.sample_valid t)

def budget (q : Rat) : Rat := qabs (((EulerReal.sample (qabs q)).compute 0).hi)+1

theorem budget_pos (q : Rat) : 0<budget q := by
  have h := qabs_nonneg (((EulerReal.sample (qabs q)).compute 0).hi)
  unfold budget; grind only

private theorem bounded (q t : Rat) (ht : t≤qabs q) : Small (value t) (budget q) := by
  have hM : (EulerReal.sample (qabs q)).Le (RealCompute.ofRat (budget q)) := by
    intro i j
    have h := RealCompute.le_refl _ (EulerReal.sample_valid (qabs q)) i 0
    have hA := self_le_qabs (((EulerReal.sample (qabs q)).compute 0).hi)
    change ((EulerReal.sample (qabs q)).compute i).lo≤budget q
    unfold budget
    grind only
  have hu := RealCompute.le_trans (EulerReal.sample_valid (qabs q)) (EulerReal.sample_mono ht) hM
  have hp := EulerReal.eval_positive (x := RealCompute.ofRat t) (RealCompute.ofRat_valid t)
  obtain ⟨k,hk⟩ := hp
  constructor
  · intro i j
    have h := RealCompute.le_refl _ (EulerReal.sample_valid t) k j
    have hb := budget_pos q
    change 0<((EulerReal.sample t).compute k).lo at hk
    change -(budget q)≤((EulerReal.sample t).compute j).hi
    grind only
  · exact hu

private theorem cancel (u v : Rat) (huv : u<v) :
    (scale (v-u) (scale (1/(v-u)) (sub (value v) (value u)))).real.preferred.Equiv
      (sub (value v) (value u)).real.preferred := by
  have hc := Rat.mul_inv_cancel (v-u) (by grind only : v-u≠0)
  apply arithmetic_identity; intro s
  simp only [scale]
  simp only [Rat.div_def,Rat.one_mul]
  rw [←Rat.mul_assoc,hc,Rat.one_mul]

/-- Supporting increments of the actual Euler construction. -/
theorem supports (u v : Rat) (huv : u<v) :
    LE (scale (v-u) (value u)) (sub (value v) (value u)) ∧
    LE (sub (value v) (value u)) (scale (v-u) (value v)) := by
  let S := scale (1/(v-u)) (sub (value v) (value u))
  have H := EulerReal.secant_order huv
  have hl : LE (value u) S := H.1
  have hu : LE S (value v) := H.2
  have hpos : 0≤v-u := by grind only
  have hc := cancel u v huv
  exact ⟨le_congr (le_scale hl hpos) (RealCompute.equiv_refl _ (scale (v-u) (value u)).real.valid) hc,
    le_congr (le_scale hu hpos) hc (RealCompute.equiv_refl _ (scale (v-u) (value v)).real.valid)⟩

private theorem increment_small (q u v : Rat) (huv : u≤v) (hv : v≤qabs q) :
    Small (sub (value v) (value u)) (budget q*(v-u)) := by
  by_cases he : u=v
  · subst v
    have hz := rational_small 0
    have he0 : qabs (0:Rat)=0 := by decide
    rw [he0] at hz
    have H : Small (sub (value u) (value u)) 0 := hz.congr (by
      apply arithmetic_identity; intro s; simp only [sub,Value.rational]; grind only)
    simpa only [Rat.sub_self,Rat.mul_zero] using H
  have huv' : u<v := by grind only
  have H := EulerReal.secant_order huv'
  have hu := bounded q u (Rat.le_trans huv hv)
  have hvB := bounded q v hv
  let S := scale (1/(v-u)) (sub (value v) (value u))
  have hS : Small S (budget q) :=
    ⟨RealCompute.le_trans (value u).real.valid hu.1 H.1,
      RealCompute.le_trans (value v).real.valid H.2 hvB.2⟩
  have hs := (scale_small hS (v-u)).congr (cancel u v huv')
  simpa only [qabs_eq_self_of_nonneg (show 0≤v-u by grind only),Rat.mul_comm] using hs

private theorem in_range (q t : Rat) (ht : 0≤t) (ht1 : t≤1) : q*t≤qabs q := by
  have h := rat_mul_le_mul_of_nonneg (qabs_nonneg q) (Rat.le_refl (a:=qabs q)) ht ht1
  have ha := self_le_qabs (q*t)
  rw [qabs_mul,qabs_eq_self_of_nonneg ht] at ha
  simpa only [Rat.mul_one] using Rat.le_trans ha h

def pulled (q t : Rat) : Value := value (q*t)
def derivative (q t : Rat) : Value := scale q (pulled q t)

private theorem pulled_lipschitz (q : Rat) :
    LipschitzIntegralBounds.Lipschitz (derivative q) 0 1 (qabs q*qabs q*budget q) := by
  intro u v hu huv hv
  have hu1 : u≤1 := Rat.le_trans huv hv
  have hv0 : 0≤v := Rat.le_trans hu huv
  have hdiff : 0≤v-u := by grind only
  have H : Small (sub (pulled q v) (pulled q u)) (budget q*(qabs q*(v-u))) := by
    by_cases hq : 0≤q
    · have hs := increment_small q (q*u) (q*v) (Rat.mul_le_mul_of_nonneg_left huv hq) (in_range q v hv0 hv)
      have he : q*v-q*u=q*(v-u) := by grind only
      simpa only [he,pulled,qabs_eq_self_of_nonneg hq] using hs
    · have hq' : q≤0 := Rat.le_of_lt (by grind only)
      have hs := (increment_small q (q*v) (q*u) (rat_mul_le_mul_of_nonpos_left huv hq')
        (in_range q u hu hu1)).neg
      have H' : Small (sub (pulled q v) (pulled q u)) (budget q*(q*u-q*v)) := hs.congr (by
        apply arithmetic_identity; intro s; simp only [pulled,sub,Value.neg]; grind only)
      have he : q*u-q*v=qabs q*(v-u) := by rw [qabs_eq_neg_of_nonpos hq']; grind only
      simpa only [he] using H'
  have H' := scale_small H q
  have he : qabs q*(budget q*(qabs q*(v-u)))=(qabs q*qabs q*budget q)*(v-u) := by grind only
  rw [he] at H'
  apply H'.congr
  apply arithmetic_identity; intro s; simp only [derivative,scale,sub]; grind only

private theorem pulled_supports (q u v : Rat) (huv : u<v) :
    LE (scale (v-u) (derivative q u)) (sub (pulled q v) (pulled q u)) ∧
    LE (sub (pulled q v) (pulled q u)) (scale (v-u) (derivative q v)) := by
  by_cases hz : q=0
  · subst q
    have eqI : (Value.rational 0).real.preferred.Equiv (sub (pulled 0 v) (pulled 0 u)).real.preferred := by
      apply arithmetic_identity; intro s; simp only [Value.rational,pulled,Rat.zero_mul,sub]; grind only
    have eqD (t : Rat) : (Value.rational 0).real.preferred.Equiv (scale (v-u) (derivative 0 t)).real.preferred := by
      apply arithmetic_identity; intro s; simp only [Value.rational,derivative,scale,Rat.zero_mul,Rat.mul_zero]
    have h0 : LE (Value.rational 0) (Value.rational 0) := fun _ _ => Rat.le_refl
    exact ⟨le_congr h0 (eqD u) eqI,le_congr h0 eqI (eqD v)⟩
  by_cases hq : 0<q
  · have H := supports (q*u) (q*v) (Rat.mul_lt_mul_of_pos_left huv hq)
    have eL : (scale (q*v-q*u) (value (q*u))).real.preferred.Equiv
        (scale (v-u) (derivative q u)).real.preferred := by
      apply arithmetic_identity; intro s; simp only [derivative,pulled,scale]; grind only
    have eU : (scale (q*v-q*u) (value (q*v))).real.preferred.Equiv
        (scale (v-u) (derivative q v)).real.preferred := by
      apply arithmetic_identity; intro s; simp only [derivative,pulled,scale]; grind only
    have ei := RealCompute.equiv_refl (sub (pulled q v) (pulled q u)).real.preferred (sub (pulled q v) (pulled q u)).real.valid
    exact ⟨le_congr H.1 eL ei,le_congr H.2 ei eU⟩
  · have hqN : q<0 := by grind only
    have H := supports (q*v) (q*u) (by have := Rat.mul_lt_mul_of_pos_left huv (show 0< -q by grind only); grind only)
    have Hlow : LE (Value.neg (scale (q*u-q*v) (value (q*u))))
        (Value.neg (sub (value (q*u)) (value (q*v)))) := RealCompute.le_neg_le_neg H.2
    have Hhigh : LE (Value.neg (sub (value (q*u)) (value (q*v))))
        (Value.neg (scale (q*u-q*v) (value (q*v)))) := RealCompute.le_neg_le_neg H.1
    have eL : (Value.neg (scale (q*u-q*v) (value (q*u)))).real.preferred.Equiv
        (scale (v-u) (derivative q u)).real.preferred := by
      apply arithmetic_identity; intro s; simp only [derivative,pulled,scale,Value.neg]; grind only
    have eU : (Value.neg (scale (q*u-q*v) (value (q*v)))).real.preferred.Equiv
        (scale (v-u) (derivative q v)).real.preferred := by
      apply arithmetic_identity; intro s; simp only [derivative,pulled,scale,Value.neg]; grind only
    have eI : (Value.neg (sub (value (q*u)) (value (q*v)))).real.preferred.Equiv
        (sub (pulled q v) (pulled q u)).real.preferred := by
      apply arithmetic_identity; intro s; simp only [pulled,sub,Value.neg]; grind only
    exact ⟨le_congr Hlow eL eI,le_congr Hhigh eI eU⟩

/-- The affine pullback of the actual Euler solution, for either sign of q. -/
def pulledStep (q : Rat) : Step (pulled q) (derivative q) 0 1 :=
  Step.ofSupportingIncrements (pulled q) (derivative q) 0 1 (qabs q*qabs q*budget q)
    (Rat.mul_nonneg (Rat.mul_nonneg (qabs_nonneg q) (qabs_nonneg q)) (Rat.le_of_lt (budget_pos q)))
    (pulled_lipschitz q) (fun u v _ huv _ => pulled_supports q u v huv)

/-- Normalize the value budget, leaving the derivative powers explicit. -/
def family (q C : Rat) (k : Nat) (t : Rat) : Value := scale (q^k) (scale (1/budget C) (pulled q t))

def family_step (q C : Rat) (k : Nat) : Step (family q C k) (family q C (k+1)) 0 1 := by
  apply (((pulledStep q).scale (1/budget C)).scale (q^k)).congr
  · intro t; exact RealCompute.equiv_refl _ (family q C k t).real.valid
  · intro t
    apply arithmetic_identity; intro s
    simp only [family,derivative,scale,Rat.pow_succ]
    grind only

private theorem abs_power (q : Rat) (k : Nat) : qabs (q^k)=(qabs q)^k := by
  induction k with
  | zero => rw [Rat.pow_zero,Rat.pow_zero]; decide +kernel
  | succ k ih => rw [Rat.pow_succ,qabs_mul,ih,Rat.pow_succ]

theorem family_bound (q C : Rat) (hqC : qabs q≤qabs C) (k : Nat) (t : Rat) (ht : 0≤t) (ht1 : t≤1) :
    Small (family q C k t) ((qabs q)^k) := by
  have H := bounded C (q*t) (Rat.le_trans (in_range q t ht ht1) hqC)
  have hb := budget_pos C
  have hi : 0≤1/budget C := by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr hb)
  have H' := H.scale_nonnegative hi
  have hc : (1/budget C)*budget C=1 := by
    rw [Rat.div_def,Rat.one_mul]; exact Rat.inv_mul_cancel _ (Rat.ne_of_gt hb)
  rw [hc] at H'
  have H'' := scale_small H' (q^k)
  simpa only [family,pulled,abs_power,Rat.mul_one] using H''

/-- Every successive remainder is the actual integral supplied by repeated
FTC for the Euler derivative family. -/
theorem remainder_integral (q C : Rat) (hqC : qabs q≤qabs C) (n k : Nat) (t : Rat) (ht : 0≤t) (ht1 : t≤1) :
    Integral.HasIntegral (LipschitzIntegralBounds.onInterval (RepeatedFTC.remainder (family q C) n (k+1)) 0 t)
      (RepeatedFTC.remainder (family q C) (n+1) k t).real.preferred :=
  RepeatedFTC.remainder_hasIntegral (family q C) (family_step q C) (qabs q) (qabs_nonneg q)
    (family_bound q C hqC) n k t ht ht1

/-- Certified factorial remainder, generated from the actual ODE solution
by repeated FTC, rather than by a proposed infinite series. -/
theorem remainder_bound (q C : Rat) (hqC : qabs q≤qabs C) (n : Nat) :
    Small (RepeatedFTC.remainder (family q C) n 0 1) ((qabs q)^n/factorialRat n) := by
  have H := RepeatedFTC.remainder_bound (family q C) (family_step q C) (qabs q) (qabs_nonneg q)
    (family_bound q C hqC) n 0 1 (by decide) (by decide)
  have one_power : (1:Rat)^n=1 := by
    clear H
    induction n with
    | zero => rfl
    | succ n ih => rw [Rat.pow_succ,ih,Rat.one_mul]
  simpa only [Nat.zero_add,FTCMonomials.term,one_power,Rat.div_def,Rat.one_mul] using H

private theorem initial (q C : Rat) (k : Nat) :
    (family q C k 0).real.preferred.Equiv (Value.rational (q^k/budget C)).real.preferred := by
  have H := RealCompute.scaleRat_equiv (r := q^k)
    (RealCompute.scaleRat_equiv (r := 1/budget C) EulerReal.sample_zero)
  have hv := (scale (q^k) (scale (1/budget C) (Value.rational 1))).real.valid
  have he : (family q C k 0).real.preferred.Equiv
      (scale (q^k) (scale (1/budget C) (Value.rational 1))).real.preferred := by
    change (RealCompute.scaleRat (q^k) (RealCompute.scaleRat (1/budget C) (EulerReal.sample (q*0)))).Equiv
      (RealCompute.scaleRat (q^k) (RealCompute.scaleRat (1/budget C) (RealCompute.ofRat 1)))
    rw [Rat.mul_zero]
    exact H
  apply RealCompute.equiv_trans (z := (Value.rational (q^k/budget C)).real.preferred)
    (family q C k 0).real.valid hv (Value.rational (q^k/budget C)).real.valid he
  apply arithmetic_identity; intro s
  simp only [scale,Value.rational,Rat.div_def,Rat.one_mul,Rat.mul_one]

theorem polynomial_identify (q C : Rat) (N : Nat) :
    (RepeatedFTC.polynomial (family q C) N 0 1).real.preferred.Equiv
      (Value.rational (EulerSeriesFinite.factorialPrefix q N/budget C)).real.preferred := by
  induction N with
  | zero =>
    apply arithmetic_identity; intro s
    change (0:Rat)=0/budget C
    simp only [Rat.div_def,Rat.zero_mul]
  | succ n ih =>
    have he := RealCompute.scaleRat_equiv (r := FTCMonomials.term n 1) (initial q C n)
    have H := RealCompute.add_equiv (RepeatedFTC.polynomial (family q C) n 0 1).real.valid
      (Value.rational (EulerSeriesFinite.factorialPrefix q n/budget C)).real.valid
      (scale (FTCMonomials.term n 1) (family q C n 0)).real.valid
      (scale (FTCMonomials.term n 1) (Value.rational (q^n/budget C))).real.valid ih he
    apply RealCompute.equiv_trans (z := (Value.rational (EulerSeriesFinite.factorialPrefix q (n+1)/budget C)).real.preferred)
      (RepeatedFTC.polynomial (family q C) (n+1) 0 1).real.valid
      (Value.add (Value.rational (EulerSeriesFinite.factorialPrefix q n/budget C))
        (scale (FTCMonomials.term n 1) (Value.rational (q^n/budget C)))).real.valid
      (Value.rational (EulerSeriesFinite.factorialPrefix q (n+1)/budget C)).real.valid (by
        simp only [RepeatedFTC.polynomial,Nat.zero_add]
        exact H)
    have one_power : (1:Rat)^n=1 := by
      clear ih he H
      induction n with
      | zero => rfl
      | succ n ih => rw [Rat.pow_succ,ih,Rat.one_mul]
    apply arithmetic_identity; intro s
    simp only [Value.add,Value.rational,scale,FTCMonomials.term,one_power,
      EulerSeriesFinite.factorialPrefix,EulerSeriesFinite.term,Rat.div_def]
    grind only

/-- The (n)-th Picard iterate for (y'=q y, y(0)=1), expressed by the
successive definite integrations in `RepeatedFTC`. The indexing starts at
one, so stage zero is the initial constant function (1). -/
def picardIterate (q C : Rat) (n : Nat) (t : Rat) : Value :=
  scale (budget C) (RepeatedFTC.polynomial (family q C) (n+1) 0 t)

/-- At rational inputs the integral iterates are the usual finite factorial
prefixes. The identification is exact; the iterates themselves were generated
by the repeated-FTC construction, not postulated as a series. -/
theorem picardIterate_at_one (q C : Rat) (n : Nat) :
    (picardIterate q C n 1).real.preferred.Equiv
      (Value.rational (EulerSeriesFinite.factorialPrefix q (n+1))).real.preferred := by
  have h := RealCompute.scaleRat_equiv (r := budget C) (polynomial_identify q C (n+1))
  apply RealCompute.equiv_trans (z := (Value.rational (EulerSeriesFinite.factorialPrefix q (n+1))).real.preferred)
    (picardIterate q C n 1).real.valid
    (scale (budget C)
      (Value.rational (EulerSeriesFinite.factorialPrefix q (n+1)/budget C))).real.valid
    (Value.rational (EulerSeriesFinite.factorialPrefix q (n+1))).real.valid h
  apply arithmetic_identity; intro s
  simp only [picardIterate,scale,Value.rational,Rat.div_def]
  rw [Rat.mul_comm (EulerSeriesFinite.factorialPrefix q (n+1)),←Rat.mul_assoc,
    Rat.mul_inv_cancel (budget C) (Rat.ne_of_gt (budget_pos C)),Rat.one_mul]

/-- Finite factorial Taylor error of the original Euler solution, derived
by repeated FTC, uniformly for rational q in the supplied bounded segment. -/
theorem rational_remainder (q C : Rat) (hqC : qabs q≤qabs C) (N : Nat) :
    Small (sub (value q) (Value.rational (EulerSeriesFinite.factorialPrefix q N)))
      (budget C*((qabs q)^N/factorialRat N)) := by
  have H := (remainder_bound q C hqC N).scale_nonnegative (Rat.le_of_lt (budget_pos C))
  have hc := Rat.mul_inv_cancel (budget C) (Rat.ne_of_gt (budget_pos C))
  have heF : (scale (budget C) (family q C 0 1)).real.preferred.Equiv (value q).real.preferred := by
    apply arithmetic_identity; intro s
    simp only [family,pulled,scale,Rat.pow_zero,Rat.one_mul,Rat.mul_one,Rat.div_def]
    rw [←Rat.mul_assoc,hc,Rat.one_mul]
  have heP := RealCompute.scaleRat_equiv (r := budget C) (polynomial_identify q C N)
  have heP' : (scale (budget C) (RepeatedFTC.polynomial (family q C) N 0 1)).real.preferred.Equiv
      (Value.rational (EulerSeriesFinite.factorialPrefix q N)).real.preferred := by
    apply RealCompute.equiv_trans (z := (Value.rational (EulerSeriesFinite.factorialPrefix q N)).real.preferred)
      (scale (budget C) (RepeatedFTC.polynomial (family q C) N 0 1)).real.valid
      (scale (budget C) (Value.rational (EulerSeriesFinite.factorialPrefix q N/budget C))).real.valid
      (Value.rational (EulerSeriesFinite.factorialPrefix q N)).real.valid heP
    apply arithmetic_identity; intro s
    simp only [scale,Value.rational,Rat.div_def]
    rw [Rat.mul_comm (EulerSeriesFinite.factorialPrefix q N),←Rat.mul_assoc,hc,Rat.one_mul]
  have heSub : (scale (budget C) (RepeatedFTC.remainder (family q C) N 0 1)).real.preferred.Equiv
      (sub (scale (budget C) (family q C 0 1))
        (scale (budget C) (RepeatedFTC.polynomial (family q C) N 0 1))).real.preferred := by
    apply arithmetic_identity; intro s; simp only [RepeatedFTC.remainder,sub,scale]; grind only
  apply H.congr
  exact RealCompute.equiv_trans (scale (budget C) (RepeatedFTC.remainder (family q C) N 0 1)).real.valid
    (sub (scale (budget C) (family q C 0 1)) (scale (budget C) (RepeatedFTC.polynomial (family q C) N 0 1))).real.valid
    (sub (value q) (Value.rational (EulerSeriesFinite.factorialPrefix q N))).real.valid heSub
    (RealCompute.sub_equiv (scale (budget C) (family q C 0 1)).real.valid (value q).real.valid
      (scale (budget C) (RepeatedFTC.polynomial (family q C) N 0 1)).real.valid (RealCompute.ofRat_valid _) heF heP')

/-- A Picard iterate's error at time one, certified by the actual repeated
FTC remainder. This supplies the convergence estimate for the IVP solution. -/
theorem picard_error (q C : Rat) (hqC : qabs q≤qabs C) (n : Nat) :
    Small (sub (value q) (picardIterate q C n 1))
      (budget C*((qabs q)^(n+1)/factorialRat (n+1))) := by
  have h := rational_remainder q C hqC (n+1)
  apply h.congr
  exact RealCompute.sub_equiv (value q).real.valid (value q).real.valid
    (Value.rational (EulerSeriesFinite.factorialPrefix q (n+1))).real.valid
    (picardIterate q C n 1).real.valid (RealCompute.equiv_refl _ (value q).real.valid)
    (RealCompute.equiv_symm (picardIterate_at_one q C n))

end ComputableAnalysis.EulerTaylorFTC


