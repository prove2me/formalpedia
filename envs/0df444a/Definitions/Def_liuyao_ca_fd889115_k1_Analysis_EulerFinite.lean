-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_EulerFinite
-- name    : liuyao_ca_fd889115_k1_Analysis_EulerFinite
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:25.242061+00:00
-- url     : https://prove2.me/theorems/f123b91f-f921-4ae2-a1e0-e5cbc00017ef
-- title:
--   Computable analysis · EulerFinite · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/EulerFinite.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-! Finite rational algebra for Euler's method. No exponential or series is
used in these identities and enclosure estimates. -/
namespace ComputableAnalysis.EulerFinite
set_option maxHeartbeats 1000000

theorem pow_add (a : Rat) (m n : Nat) : a^(m+n)=a^m*a^n := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih => simp only [Nat.add_succ,Rat.pow_succ,ih]; grind only

theorem mul_pow (a b : Rat) (n : Nat) : (a*b)^n=a^n*b^n := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih => simp only [Rat.pow_succ,ih]; grind only

theorem pow_mul (a : Rat) (m n : Nat) : a^(m*n)=(a^m)^n := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih => rw [Nat.mul_succ,pow_add,ih,Rat.pow_succ]

theorem pow_mono {a b : Rat} (ha : 0≤a) (hab : a≤b) (n : Nat) : a^n≤b^n := by
  induction n with
  | zero => simp [Rat.pow_zero]
  | succ n ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact rat_mul_le_mul_of_nonneg (Rat.pow_nonneg ha) ih ha hab

theorem pow_pos {a : Rat} (ha : 0<a) (n : Nat) : 0<a^n := by
  induction n with
  | zero => simpa only [Rat.pow_zero] using (show (0:Rat)<1 by decide +kernel)
  | succ n ih => rw [Rat.pow_succ]; exact Rat.mul_pos ih ha

theorem inv_antitone {a b : Rat} (ha : 0<a) (hab : a≤b) : b⁻¹≤a⁻¹ := by
  have hb : 0<b := by grind only
  have A := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
  have B := Rat.mul_inv_cancel b (Rat.ne_of_gt hb)
  have H := Rat.mul_le_mul_of_nonneg_right hab
    (Rat.mul_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr ha)) (Rat.le_of_lt (Rat.inv_pos.mpr hb)))
  have hleft : a*(a⁻¹*b⁻¹)=b⁻¹ := by rw [←Rat.mul_assoc,A,Rat.one_mul]
  have hright : b*(a⁻¹*b⁻¹)=a⁻¹ := by
    calc
      _=a⁻¹*(b*b⁻¹) := by grind only
      _=a⁻¹ := by rw [B,Rat.mul_one]
  rw [hleft,hright] at H
  exact H

/-- A finite geometric sum, with both endpoint bases visible. -/
def mixed (a b : Rat) : Nat → Rat
  | 0 => 0
  | n+1 => a^n+b*mixed a b n

theorem mixed_identity (a b : Rat) (n : Nat) :
    (a-b)*mixed a b n=a^n-b^n := by
  induction n with
  | zero => simp only [mixed,Rat.pow_zero]; grind only
  | succ n ih => simp only [mixed,Rat.pow_succ]; grind only

theorem mixed_bounds {a b : Rat} (hb : 0≤b) (hba : b≤a) (n : Nat) :
    ((n+1:Nat):Rat)*b^n≤mixed a b (n+1) ∧
      mixed a b (n+1)≤((n+1:Nat):Rat)*a^n := by
  have ha : 0≤a := Rat.le_trans hb hba
  induction n with
  | zero => simp only [mixed,Rat.pow_zero]; constructor <;> grind only
  | succ n ih =>
    have hp := pow_mono hb hba (n+1)
    have hn : 0≤((n+1:Nat):Rat) := Rat.natCast_nonneg
    have Hlo := Rat.mul_le_mul_of_nonneg_left ih.1 hb
    have Hhi := Rat.mul_le_mul_of_nonneg_left ih.2 hb
    have Hbase := Rat.mul_le_mul_of_nonneg_right hba
      (Rat.mul_nonneg hn (Rat.pow_nonneg (n := n) ha))
    simp only [mixed] at *
    simp only [Rat.pow_succ] at hp ⊢
    have hc : ((n+1+1:Nat):Rat)=((n+1:Nat):Rat)+1 := by rw [Rat.natCast_add]; rfl
    rw [hc]
    constructor <;> grind only

def lower (q : Rat) (N : Nat) : Rat := (1+q/(N:Rat))^N
def upper (q : Rat) (N : Nat) : Rat := (lower (-q) N)⁻¹

theorem lower_positive {q : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hlo : -(N:Rat)<q) : 0<lower q N := by
  have hi : 0<(N:Rat)⁻¹ := Rat.inv_pos.mpr hN
  have h := Rat.mul_lt_mul_of_pos_right hlo hi
  have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hN)
  exact pow_pos (by grind [Rat.div_def]) N

theorem upper_positive {q : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hhi : q<(N:Rat)) : 0<upper q N :=
  Rat.inv_pos.mpr (lower_positive hN (by grind only))

theorem lower_upper_product (q : Rat) (N : Nat) :
    lower q N*lower (-q) N=(1-(q/(N:Rat))^2)^N := by
  rw [lower,lower,←mul_pow]
  congr 1
  rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_zero]
  grind [Rat.div_def]

theorem lower_le_upper {q : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hlo : -(N:Rat)<q) (hhi : q<(N:Rat)) : lower q N≤upper q N := by
  have hp := lower_positive hN hlo
  have hn := lower_positive hN (q := -q) (by grind only)
  have hs : 0≤1-(q/(N:Rat))^2 := by
    have hi : 0<(N:Rat)⁻¹ := Rat.inv_pos.mpr hN
    have h1 := Rat.mul_lt_mul_of_pos_right hlo hi
    have h2 := Rat.mul_lt_mul_of_pos_right hhi hi
    have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hN)
    have H := Rat.mul_nonneg (show 0≤1+q/(N:Rat) by grind [Rat.div_def])
      (show 0≤1-q/(N:Rat) by grind [Rat.div_def])
    rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_zero]
    grind only
  have hsmall : 1-(q/(N:Rat))^2≤1 := by
    have := rat_square_nonneg_basic (q/(N:Rat))
    rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_zero]
    grind only
  have H := pow_mono hs hsmall N
  have hprod := lower_upper_product q N
  have hone : ∀ n : Nat,(1:Rat)^n=1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Rat.pow_succ,ih,Rat.mul_one]
  rw [hone N] at H
  have hc := Rat.mul_inv_cancel (lower (-q) N) (Rat.ne_of_gt hn)
  apply Rat.le_of_mul_le_mul_right (c := lower (-q) N) _ hn
  dsimp [upper]
  grind only

theorem eq_of_mul_eq {a b c : Rat} (hc : c≠0) (h : a*c=b*c) : a=b := by
  have H := congrArg (fun t : Rat => t*c⁻¹) h
  have C := Rat.mul_inv_cancel c hc
  simpa only [Rat.mul_assoc,C,Rat.mul_one] using H

theorem div_mul (q a b : Rat) (ha : a≠0) (hb : b≠0) : q/(a*b)=(q/a)/b := by
  have hab : a*b≠0 := by intro h; rcases Rat.mul_eq_zero.mp h with h|h <;> contradiction
  apply eq_of_mul_eq hab
  rw [Rat.div_mul_cancel hab]
  have h1 := Rat.div_mul_cancel (a := q/a) hb
  have h2 := Rat.div_mul_cancel (a := q) ha
  calc
    q=(q/a)*a := h2.symm
    _=(((q/a)/b)*b)*a := by rw [h1]
    _=((q/a)/b)*(a*b) := by grind only

theorem half_mesh (q : Rat) {N : Nat} (hN : 0<(N:Rat)) :
    q/((2*N:Nat):Rat)=(q/(N:Rat))/2 := by
  rw [Rat.natCast_mul]
  change q/(2*(N:Rat))=q/(N:Rat)/2
  rw [Rat.mul_comm (2:Rat),div_mul q (N:Rat) 2 (Rat.ne_of_gt hN) (by decide +kernel)]

theorem lower_double {q : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hlo : -(N:Rat)<q) : lower q N≤lower q (2*N) := by
  have hbase : 0≤1+q/(N:Rat) := by
    have h := Rat.mul_lt_mul_of_pos_right hlo (Rat.inv_pos.mpr hN)
    have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hN)
    grind [Rat.div_def]
  have hsq : 1+q/(N:Rat)≤(1+q/((2*N:Nat):Rat))^2 := by
    rw [half_mesh q hN,Rat.pow_succ,Rat.pow_succ,Rat.pow_zero]
    have H := rat_square_nonneg_basic (q/(N:Rat))
    grind [Rat.div_def]
  have H := pow_mono hbase hsq N
  simpa only [lower,pow_mul] using H

theorem upper_double {q : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hhi : q<(N:Rat)) : upper q (2*N)≤upper q N := by
  exact inv_antitone (lower_positive hN (q := -q) (by grind only))
    (lower_double hN (q := -q) (by grind only))

theorem one_sub_power_le {u : Rat} (hu : 0≤u) (hu1 : u≤1) (n : Nat) :
    1-(1-u)^n≤(n:Rat)*u := by
  induction n with
  | zero => simp only [Rat.pow_zero]; grind only
  | succ n ih =>
    have H := Rat.mul_le_mul_of_nonneg_right ih (show 0≤1-u by grind only)
    have hs := Rat.mul_nonneg (Rat.natCast_nonneg (a := n)) (Rat.mul_nonneg hu hu)
    rw [Rat.pow_succ,Rat.natCast_add]
    change 1-(1-u)^n*(1-u)≤((n:Rat)+1)*u
    grind only

theorem mesh_square_count (q : Rat) {N : Nat} (hN : 0<(N:Rat)) :
    (N:Rat)*(q/(N:Rat))^2=q^2/(N:Rat) := by
  have hn := Rat.ne_of_gt hN
  apply eq_of_mul_eq hn
  rw [Rat.div_mul_cancel hn]
  have h := Rat.div_mul_cancel (a := q) hn
  calc
    (N:Rat)*(q/(N:Rat))^2*(N:Rat)=((q/(N:Rat))*(N:Rat))^2 := by
      simp only [Rat.pow_succ,Rat.pow_zero]; grind only
    _=q^2 := by rw [h]

theorem gap_bound {q : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hlo : -(N:Rat)<q) (hhi : q<(N:Rat)) :
    upper q N-lower q N≤upper q N*(q^2/(N:Rat)) := by
  have hn := lower_positive hN (q := -q) (by grind only)
  have hu := Rat.le_of_lt (upper_positive hN hhi)
  have h1 := Rat.mul_lt_mul_of_pos_right hlo (Rat.inv_pos.mpr hN)
  have h2 := Rat.mul_lt_mul_of_pos_right hhi (Rat.inv_pos.mpr hN)
  have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hN)
  have hbase : 0≤1+q/(N:Rat) := by grind [Rat.div_def]
  have hbase' : 0≤1-q/(N:Rat) := by grind [Rat.div_def]
  have hprod := Rat.mul_nonneg hbase hbase'
  have hs : (q/(N:Rat))^2≤1 := by
    simp only [Rat.pow_succ,Rat.pow_zero]; grind only
  have H := one_sub_power_le (u := (q/(N:Rat))^2)
    (by simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] using rat_square_nonneg_basic (q/(N:Rat))) hs N
  have Hmul := Rat.mul_le_mul_of_nonneg_left H hu
  rw [mesh_square_count q hN] at Hmul
  have hid := lower_upper_product q N
  have hcancel : upper q N*lower (-q) N=1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt hn)
  have he : upper q N*(1-(1-(q/(N:Rat))^2)^N)=upper q N-lower q N := by
    rw [←hid]
    calc
      _=upper q N-lower q N*(upper q N*lower (-q) N) := by grind only
      _=upper q N-lower q N := by rw [hcancel,Rat.mul_one]
  rw [he] at Hmul
  exact Hmul

theorem bernoulli {t : Rat} (ht : -1≤t) (n : Nat) : 1+(n:Rat)*t≤(1+t)^n := by
  induction n with
  | zero => simp only [Rat.pow_zero]; grind only
  | succ n ih =>
    have H := Rat.mul_le_mul_of_nonneg_right ih (show 0≤1+t by grind only)
    have hs := Rat.mul_nonneg (Rat.natCast_nonneg (a := n)) (rat_square_nonneg_basic t)
    rw [Rat.pow_succ,Rat.natCast_add]
    change 1+((n:Rat)+1)*t≤(1+t)^n*(1+t)
    grind only

theorem lower_mono {a b : Rat} {N : Nat} (hN : 0<(N:Rat))
    (ha : -(N:Rat)<a) (hab : a≤b) : lower a N≤lower b N := by
  have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hN)
  have h := Rat.mul_lt_mul_of_pos_right ha (Rat.inv_pos.mpr hN)
  have h' := Rat.mul_le_mul_of_nonneg_right hab (Rat.le_of_lt (Rat.inv_pos.mpr hN))
  apply pow_mono
  · grind [Rat.div_def]
  · grind [Rat.div_def]

theorem upper_mono {a b : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hb : b<(N:Rat)) (hab : a≤b) : upper a N≤upper b N :=
  inv_antitone (lower_positive hN (q := -b) (by grind only))
    (lower_mono hN (a := -b) (b := -a) (by grind only) (by grind only))

theorem lower_refine {q : Rat} {N K : Nat} (hN : 0<(N:Rat)) (hK : 0<K)
    (hlo : -(N:Rat)<q) : lower q N≤lower q (N*K) := by
  have hk : 0<(K:Rat) := Rat.natCast_pos.mpr hK
  have hk1 : (1:Rat)≤(K:Rat) := by exact_mod_cast hK
  have hnk : 0<((N*K:Nat):Rat) := by rw [Rat.natCast_mul]; exact Rat.mul_pos hN hk
  have hnle : (N:Rat)≤((N*K:Nat):Rat) := by
    rw [Rat.natCast_mul]
    have h := Rat.mul_le_mul_of_nonneg_left hk1 (Rat.le_of_lt hN)
    simpa only [Rat.mul_one] using h
  have hbase : 0≤1+q/((N*K:Nat):Rat) := by
    have h := Rat.mul_lt_mul_of_pos_right (show -((N*K:Nat):Rat)<q by grind only)
      (Rat.inv_pos.mpr hnk)
    have hc := Rat.mul_inv_cancel ((N*K:Nat):Rat) (Rat.ne_of_gt hnk)
    grind [Rat.div_def]
  have hb := bernoulli (t := q/((N*K:Nat):Rat)) (by grind only) K
  have hd : (K:Rat)*(q/((N*K:Nat):Rat))=q/(N:Rat) := by
    rw [Rat.natCast_mul,div_mul q (N:Rat) (K:Rat) (Rat.ne_of_gt hN) (Rat.ne_of_gt hk)]
    have hc := Rat.div_mul_cancel (a := q/(N:Rat)) (Rat.ne_of_gt hk)
    grind only
  rw [hd] at hb
  have hcoarse : 0≤1+q/(N:Rat) := by
    have h := Rat.mul_lt_mul_of_pos_right hlo (Rat.inv_pos.mpr hN)
    have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hN)
    grind [Rat.div_def]
  have H := pow_mono hcoarse hb N
  change (1+q/(N:Rat))^N≤(1+q/((N*K:Nat):Rat))^(N*K)
  have he : (1+q/((N*K:Nat):Rat))^(N*K)=((1+q/((N*K:Nat):Rat))^K)^N := by
    calc
      _=(1+q/((N*K:Nat):Rat))^(K*N) :=
        congrArg (fun k => (1+q/((N*K:Nat):Rat))^k) (Nat.mul_comm N K)
      _=_ := pow_mul _ K N
  rw [he]
  exact H

theorem upper_refine {q : Rat} {N K : Nat} (hN : 0<(N:Rat)) (hK : 0<K)
    (hhi : q<(N:Rat)) : upper q (N*K)≤upper q N :=
  inv_antitone (lower_positive hN (q := -q) (by grind only))
    (lower_refine hN hK (q := -q) (by grind only))

/-- Common refinement compares two independent mesh choices. -/
theorem cross_bound {a b : Rat} {N K : Nat} (hN : 0<(N:Rat)) (hK : 0<(K:Rat))
    (ha : -(N:Rat)<a) (hb : b<(K:Rat)) (hab : a≤b) : lower a N≤upper b K := by
  have hn : 0<N := Rat.natCast_pos.mp hN
  have hk : 0<K := Rat.natCast_pos.mp hK
  have hn1 : (1:Rat)≤(N:Rat) := by exact_mod_cast hn
  have hk1 : (1:Rat)≤(K:Rat) := by exact_mod_cast hk
  have hnk : 0<((N*K:Nat):Rat) := by rw [Rat.natCast_mul]; exact Rat.mul_pos hN hK
  have hnl : (N:Rat)≤((N*K:Nat):Rat) := by
    rw [Rat.natCast_mul]
    have h := Rat.mul_le_mul_of_nonneg_left hk1 (Rat.le_of_lt hN)
    simpa only [Rat.mul_one] using h
  have hkl : (K:Rat)≤((N*K:Nat):Rat) := by
    rw [Rat.natCast_mul]
    have h := Rat.mul_le_mul_of_nonneg_right hn1 (Rat.le_of_lt hK)
    simpa only [Rat.one_mul] using h
  calc
    lower a N≤lower a (N*K) := lower_refine hN hk ha
    _≤lower b (N*K) := lower_mono hnk (by grind only) hab
    _≤upper b (N*K) := lower_le_upper hnk (by grind only) (by grind only)
    _=upper b (K*N) := by rw [Nat.mul_comm N K]
    _≤upper b K := upper_refine hK hn hb

theorem base_positive {q : Rat} {N : Nat} (hN : 0<(N:Rat))
    (hq : -(N:Rat)<q) : 0<1+q/(N:Rat) := by
  have h := Rat.mul_lt_mul_of_pos_right hq (Rat.inv_pos.mpr hN)
  have hc := Rat.mul_inv_cancel (N:Rat) (Rat.ne_of_gt hN)
  grind [Rat.div_def]

/-- The exact finite difference-of-powers enclosure for a forward Euler mesh. -/
theorem lower_difference_bounds {a b : Rat} (n : Nat)
    (ha : -((n+1:Nat):Rat)<a) (hab : a≤b) :
    (b-a)*(1+a/((n+1:Nat):Rat))^n≤lower b (n+1)-lower a (n+1) ∧
      lower b (n+1)-lower a (n+1)≤(b-a)*(1+b/((n+1:Nat):Rat))^n := by
  let N := n+1
  have hN : 0<(N:Rat) := Rat.natCast_pos.mpr (Nat.succ_pos n)
  let A := 1+b/(N:Rat)
  let B := 1+a/(N:Rat)
  have hb : 0≤B := Rat.le_of_lt (base_positive hN ha)
  have habase : B≤A := by
    have H := Rat.mul_le_mul_of_nonneg_right hab (Rat.le_of_lt (Rat.inv_pos.mpr hN))
    dsimp [A,B]; grind [Rat.div_def]
  have H := mixed_bounds hb habase n
  have Hmul := mixed_identity A B N
  have he : A-B=(b-a)/(N:Rat) := by dsimp [A,B]; grind [Rat.div_def]
  rw [he] at Hmul
  have hnum : 0≤(b-a)/(N:Rat) := by
    exact Rat.mul_nonneg (by grind only) (Rat.le_of_lt (Rat.inv_pos.mpr hN))
  have Hl := Rat.mul_le_mul_of_nonneg_left H.1 hnum
  have Hu := Rat.mul_le_mul_of_nonneg_left H.2 hnum
  have hc := Rat.div_mul_cancel (a := b-a) (Rat.ne_of_gt hN)
  have cancel (v : Rat) : ((b-a)/(N:Rat))*((N:Rat)*v)=(b-a)*v := by
    rw [←Rat.mul_assoc,hc]
  change (b-a)*B^n≤A^N-B^N ∧ A^N-B^N≤(b-a)*A^n
  change (b-a)/(N:Rat)*((N:Rat)*B^n)≤(b-a)/(N:Rat)*mixed A B N at Hl
  change (b-a)/(N:Rat)*mixed A B N≤(b-a)/(N:Rat)*((N:Rat)*A^n) at Hu
  rw [cancel,Hmul] at Hl
  rw [cancel,Hmul] at Hu
  exact ⟨Hl,Hu⟩

theorem lower_lipschitz {M a b : Rat} {N : Nat} (hM : 0≤M)
    (ha : -M≤a) (hab : a≤b) (hb : b≤M) (hMN : M<(N:Rat)) :
    0≤lower b N-lower a N ∧
      lower b N-lower a N≤(b-a)*upper M N := by
  have hN : 0<(N:Rat) := by grind only
  have hn : 0<N := Rat.natCast_pos.mp hN
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  subst N
  have H := lower_difference_bounds n (by grind only) hab
  have hbase : 0≤1+b/((n+1:Nat):Rat) := Rat.le_of_lt (base_positive hN (by grind only))
  have hD : (1:Rat)≤1+M/((n+1:Nat):Rat) := by
    have H := Rat.mul_nonneg hM (Rat.le_of_lt (Rat.inv_pos.mpr hN))
    grind [Rat.div_def]
  have hbD : 1+b/((n+1:Nat):Rat)≤1+M/((n+1:Nat):Rat) := by
    have H := Rat.mul_le_mul_of_nonneg_right hb (Rat.le_of_lt (Rat.inv_pos.mpr hN))
    grind [Rat.div_def]
  have hp := pow_mono hbase hbD n
  have hpow := Rat.mul_le_mul_of_nonneg_left hD
    (Rat.pow_nonneg (n := n) (show 0≤1+M/((n+1:Nat):Rat) by grind only))
  have hsmall := lower_le_upper hN (q := M) (by grind only) hMN
  have hpow' : (1+b/((n+1:Nat):Rat))^n≤upper M (n+1) := by
    change (1+M/((n+1:Nat):Rat))^(n+1)≤upper M (n+1) at hsmall
    rw [Rat.pow_succ] at hsmall
    rw [Rat.mul_one] at hpow
    exact Rat.le_trans hp (Rat.le_trans hpow hsmall)
  have hlo := lower_mono hN (a := a) (b := b) (by grind only) hab
  refine ⟨by grind only,?_⟩
  exact Rat.le_trans H.2 (Rat.mul_le_mul_of_nonneg_left hpow' (by grind only))

def slope (q : Rat) (N : Nat) : Rat := (1+q/(N:Rat))^(N-1)

theorem slope_bounds {M q : Rat} {N : Nat} (hM : 0≤M)
    (hqlo : -M≤q) (hqhi : q≤M) (hMN : M<(N:Rat)) :
    0≤slope q N ∧ slope q N≤upper M N := by
  have hN : 0<(N:Rat) := by grind only
  have hn := Rat.natCast_pos.mp hN
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  subst N
  have hq : 0≤1+q/((n+1:Nat):Rat) := Rat.le_of_lt (base_positive hN (by grind only))
  have hD : (1:Rat)≤1+M/((n+1:Nat):Rat) := by
    have H := Rat.mul_nonneg hM (Rat.le_of_lt (Rat.inv_pos.mpr hN))
    grind [Rat.div_def]
  have hqD : 1+q/((n+1:Nat):Rat)≤1+M/((n+1:Nat):Rat) := by
    have H := Rat.mul_le_mul_of_nonneg_right hqhi (Rat.le_of_lt (Rat.inv_pos.mpr hN))
    grind [Rat.div_def]
  have hp := pow_mono hq hqD n
  have hpow := Rat.mul_le_mul_of_nonneg_left hD
    (Rat.pow_nonneg (n := n) (show 0≤1+M/((n+1:Nat):Rat) by grind only))
  have hs := lower_le_upper hN (q := M) (by grind only) hMN
  change (1+M/((n+1:Nat):Rat))^(n+1)≤upper M (n+1) at hs
  rw [Rat.pow_succ] at hs
  rw [Rat.mul_one] at hpow
  change 0≤(1+q/((n+1:Nat):Rat))^n ∧ (1+q/((n+1:Nat):Rat))^n≤upper M (n+1)
  exact ⟨Rat.pow_nonneg hq,Rat.le_trans hp (Rat.le_trans hpow hs)⟩

theorem lower_slope_identity (q : Rat) {N : Nat} (hN : 0<N) :
    lower q N=slope q N+(q/(N:Rat))*slope q N := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  subst N
  simp only [lower,slope,Nat.add_sub_cancel,Rat.pow_succ]
  grind only

theorem lower_slope_error {M q : Rat} {N : Nat} (hM : 0≤M)
    (hqlo : -M≤q) (hqhi : q≤M) (hMN : M<(N:Rat)) :
    -(upper M N*M/(N:Rat))≤lower q N-slope q N ∧
      lower q N-slope q N≤upper M N*M/(N:Rat) := by
  have hN : 0<(N:Rat) := by grind only
  have hs := slope_bounds hM hqlo hqhi hMN
  have hl := Rat.mul_le_mul_of_nonneg_right hqlo hs.1
  have hu := Rat.mul_le_mul_of_nonneg_right hqhi hs.1
  have H := Rat.mul_le_mul_of_nonneg_left hs.2 hM
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hN)
  have Hl := Rat.mul_le_mul_of_nonneg_right (show -(upper M N*M)≤q*slope q N by grind only) hi
  have Hu := Rat.mul_le_mul_of_nonneg_right (show q*slope q N≤upper M N*M by grind only) hi
  rw [lower_slope_identity q (Rat.natCast_pos.mp hN)]
  constructor <;> grind [Rat.div_def]

theorem finite_secant_bounds {a b : Rat} {N : Nat} (hN : 0<(N:Rat))
    (ha : -(N:Rat)<a) (hab : a<b) :
    slope a N≤(lower b N-lower a N)/(b-a) ∧
      (lower b N-lower a N)/(b-a)≤slope b N := by
  have hn := Rat.natCast_pos.mp hN
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  subst N
  have H := lower_difference_bounds n ha (Rat.le_of_lt hab)
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr (show 0<b-a by grind only))
  have Hl := Rat.mul_le_mul_of_nonneg_right H.1 hi
  have Hu := Rat.mul_le_mul_of_nonneg_right H.2 hi
  have hc := Rat.mul_inv_cancel (b-a) (by grind only : b-a≠0)
  have cancel (v : Rat) : ((b-a)*v)*(b-a)⁻¹=v := by
    calc
      _=v*((b-a)*(b-a)⁻¹) := by grind only
      _=v := by rw [hc,Rat.mul_one]
  rw [cancel] at Hl Hu
  exact ⟨Hl,Hu⟩

theorem finite_chord_error {M a b : Rat} {N : Nat} (hM : 0≤M)
    (ha : -M≤a) (hab : a<b) (hb : b≤M) (hMN : M<(N:Rat)) :
    lower a N≤(lower b N-lower a N)/(b-a)+upper M N*M/(N:Rat) ∧
      (lower b N-lower a N)/(b-a)≤lower b N+upper M N*M/(N:Rat) := by
  have hN : 0<(N:Rat) := by grind only
  have H := finite_secant_bounds hN (by grind only) hab
  have Ha := lower_slope_error hM ha (by grind only) hMN
  have Hb := lower_slope_error hM (by grind only) hb hMN
  constructor <;> grind only

theorem one_pow (n : Nat) : (1:Rat)^n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Rat.pow_succ,ih,Rat.mul_one]

theorem lower_zero (N : Nat) : lower 0 N=1 := by
  simp only [lower,Rat.div_def,Rat.zero_mul,Rat.add_zero,one_pow]

theorem upper_zero (N : Nat) : upper 0 N=1 := by
  have hneg : -(0:Rat)=0 := by decide +kernel
  rw [upper,hneg,lower_zero]
  decide +kernel

end ComputableAnalysis.EulerFinite


