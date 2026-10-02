-- Prove2me | Definitions.Def_Yukon_f982a7c596fb3f4d2bc31117
-- name    : Yukon_f982a7c596fb3f4d2bc31117
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:49:20.145337+00:00
-- url     : https://prove2.me/theorems/9fb5310b-afa9-4ae3-892c-d35c9b071892
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberThresholdClosed6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberThresholdClosed6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberThresholdClosed6814.lean
--
--   yukon-proof-operation:foundation-direct-eb111e0ef6695fc77ba4f66ef80d313c2962896f40bc8c9ded92b3525f16d5d7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTQ5YmE4NjcwMGM4ZWM5Yjc0NmEzNjQwODZkZWEwZTJjMmU3NzVjYmFjMjZiNWQ2MDBkNTVjNzcxYWY2NzIwYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWViMTExZTBlZjY2OTVmYzc3YmE0ZjY2ZWY4MGQzMTNjMjk2Mjg5NmY0MGJjOGM5ZGVkOTJiMzUyNWYxNmQ1ZDciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mOTgyYTdjNTk2ZmIzZjRkMmJjMzExMTciLCJ2IjoyfQ]

import Definitions.Def_Yukon_542fee5622a1d28a6009acd1

import Definitions.Def_Yukon_db7fac091d8b13fd5e8a3a0c












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async true
namespace ProximityPrize.SubmissionLower.Lower80889.ThresholdIndexed
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (rawFlag)
open Lower80889.Oracle Lower80889.ThresholdFast
open Lower80889.PhaseRows
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def indexedThin (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => indexedThin w Dh delta dc dT dY dS T YS S n +
      delta * evalChannelCount (T-n*dT)
        (min (YS-n*dY) (thinTop w (Dh-n*(delta+dc)) (S-n*dS))) (S-n*dS)

theorem indexedThin_shift (w Dh delta dc dT dY dS T YS S n : ℕ) :
    indexedThin w Dh delta dc dT dY dS T YS S (n+1) =
      delta * evalChannelCount T (min YS (thinTop w Dh S)) S +
        indexedThin w (Dh-delta-dc) delta dc dT dY dS (T-dT) (YS-dY) (S-dS) n := by
  induction n with
  | zero => simp [indexedThin]
  | succ n ih =>
      rw [indexedThin, ih, indexedThin]
      have shift (x d : ℕ) : x-(n+1)*d = (x-d)-n*d := by
        rw [Nat.add_mul, Nat.one_mul, Nat.sub_sub]
        omega
      rw [shift T dT, shift YS dY, shift S dS, shift Dh (delta+dc)]
      rw [Nat.sub_sub]
      omega

theorem indexedThin_eq (w Dh delta dc dT dY dS T YS S fuel : ℕ) :
    indexedThin w Dh delta dc dT dY dS T YS S fuel =
      evalPowerBandBudgetThin w Dh delta dc dT dY dS T YS S fuel := by
  induction fuel generalizing Dh T YS S with
  | zero => rfl
  | succ fuel ih =>
      rw [indexedThin_shift, evalPowerBandBudgetThin, ih]

def indexedBand (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  indexedThin 131071 (s.contactCap p) 50185 (contactDec p)
    (total p) (middle p) p.all (s.totalCap-total p)
    (s.middleCap-middle p) (s.slopeCap-p.all) (s.fuel p)

theorem indexedBand_eq (s : SourceNumbers) (p : FlagDegree) :
    indexedBand s p = evalBandThin s p := indexedThin_eq _ _ _ _ _ _ _ _ _ _ _

def IndexedSufficient (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  10714-(r+v) < threshold ∨
    let p := rawFlag r v threshold
    1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
      p.all ≤ s.slopeCap ∧ indexedBand s p < s.gap
instance  _root_.ProximityPrize.SubmissionLower.Lower80889.ThresholdIndexed.instDecidableIndexedSufficient (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (IndexedSufficient s r v threshold) := by
  unfold IndexedSufficient; infer_instance

theorem sufficient_of_indexed (s : SourceNumbers) (r v threshold : ℕ)
    (h : IndexedSufficient s r v threshold) :
    FastSourceThresholdSufficient s r v threshold := by
  rcases h with h | ⟨hr,ht,hy,hs,hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr,ht,hy,hs,Or.inl ((indexedBand_eq _ _) ▸ hb)⟩

end ProximityPrize.SubmissionLower.Lower80889.ThresholdIndexed

namespace ProximityPrize.SubmissionLower.Lower80889.BandPolynomial
open scoped BigOperators
open LocatorLowQuotient Lower80889.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def boxPoly (w A B C : ℤ) : ℤ :=
  (C+w)*(3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B)

theorem choose_two_scaled (c : ℕ) :
    2 * (c+2).choose 2 = (c+2)*(c+1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (c+2) 2
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_comm] using h.symm

theorem choose_three_scaled (c : ℕ) :
    6 * (c+2).choose 3 = (c+2)*(c+1)*c := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (c+2) 3
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h.symm

theorem half_succ (c : ℕ) : 2*((c+1)*c/2) = (c+1)*c := by
  have h : 2 ∣ (c+1)*c := by
    simpa [Nat.mul_comm, Nat.add_comm] using
      (even_iff_two_dvd.mp (Nat.even_mul_succ_self c))
  simpa [Nat.mul_comm] using Nat.div_mul_cancel h

theorem half_pred (b : ℕ) : 2*(b*(b-1)/2)+b = b*b := by
  cases b with
  | zero => decide
  | succ b =>
      simp only [Nat.add_sub_cancel]
      rw [half_succ]
      ring

theorem channel_raw (a b c : ℕ) :
    6 * (channelCount (a+b+c) (b+c) c : ℤ) = boxPoly 1 a b c := by
  rw [channelCount_eq_fast]
  have hm : min (a+b+c) (b+c) = b+c := min_eq_right (by omega)
  have hk : min c (b+c) = c := min_eq_left (by omega)
  simp only [fastChannelCount, hm, hk]
  have hA : a+b+c+1-(b+c) = a+1 := by omega
  have hB : b+c-c = b := by omega
  rw [hA, hB]
  have hsub : (c+1)*c/2 ≤ (c+1)*(a+1+c+1) :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by omega))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub hsub]
  have h2 : (2 : ℤ)*((c+2).choose 2 : ℤ) = (c+2)*(c+1) := by
    exact_mod_cast choose_two_scaled c
  have h3 : (6 : ℤ)*((c+2).choose 3 : ℤ) = (c+2)*(c+1)*c := by
    exact_mod_cast choose_three_scaled c
  have hc : (2 : ℤ)*(((c+1)*c/2 : ℕ) : ℤ) = (c+1)*c := by
    exact_mod_cast half_succ c
  have hb : (2 : ℤ)*((b*(b-1)/2 : ℕ) : ℤ)+b = b*b := by
    exact_mod_cast half_pred b
  unfold boxPoly
  nlinarith only [h3, congrArg (fun x : ℤ => 3*(a+1)*x) h2,
    congrArg (fun x : ℤ => 3*(b : ℤ)*x) hc,
    congrArg (fun x : ℤ => 3*(c+1)*x) hb]


theorem channel_normalized (T YS S : ℕ) :
    channelCount T YS S =
      channelCount (T-min T YS+(min T YS-min S (min T YS))+min S (min T YS))
        (min T YS-min S (min T YS)+min S (min T YS)) (min S (min T YS)) := by
  have hU := Nat.min_le_left T YS
  have hk := Nat.min_le_right S (min T YS)
  have hT : T-min T YS+(min T YS-min S (min T YS))+min S (min T YS) = T := by omega
  have hY : min T YS-min S (min T YS)+min S (min T YS) = min T YS := by omega
  rw [hT, hY]
  rw [channelCount_eq_cappedKernel, channelCount_eq_cappedKernel]
  rw [min_eq_right hU]
  rw [kernelSumRange_eq, kernelSumRange_eq]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : x ≤ min T YS := by have := Finset.mem_range.mp hx; omega
  unfold cappedTerm
  rw [min_assoc, min_eq_right hx']

theorem channel_poly (T YS S : ℕ) :
    6*(channelCount T YS S : ℤ) =
      boxPoly 1 ((T-min T YS : ℕ) : ℤ) ((min T YS-min S (min T YS) : ℕ) : ℤ) (min S (min T YS) : ℕ) := by
  rw [channel_normalized T YS S]
  exact channel_raw _ _ _

theorem boxPoly_scaled (w a b c : ℤ) :
    boxPoly w (w*a) (w*b) (w*c) = w^3*boxPoly 1 a b c := by
  unfold boxPoly
  ring

theorem boxPoly_mono (w a b c A B C : ℤ)
    (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) :
    boxPoly w a b c ≤ boxPoly w A B C := by
  have hA0 := ha.trans hA
  have hB0 := hb.trans hB
  have hC0 := hc.trans hC
  unfold boxPoly
  gcongr <;> positivity


/-- Rounding the thin middle width costs at most one unit in the outer width. -/
theorem channel_thin_bound (T YS S Dh : ℕ) :
    6*131071^3*(channelCount T (min YS ((Dh+S-1)/131071)) S : ℤ) ≤
      boxPoly 131071
        (131071*T-min (131071*T) (min (131071*YS) (Dh+S))+131071)
        (min (131071*T) (min (131071*YS) (Dh+S))-
          min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S))))
        (min (131071*S) (min (131071*T) (min (131071*YS) (Dh+S)))) := by
  let U := min T (min YS ((Dh+S-1)/131071))
  let C := min S U
  let V : ℤ := min (131071*T) (min (131071*YS) (Dh+S))
  let K : ℤ := min (131071*S) V
  have hU : U ≤ T := Nat.min_le_left _ _
  have hC : C ≤ U := Nat.min_le_right _ _
  have hround : 131071*(U : ℤ) ≤ V ∧ V ≤ 131071*(U : ℤ)+131071 := by
    dsimp [U, V]
    omega
  have hK : 131071*(C : ℤ) ≤ K := by dsimp [C, K]; omega
  have hB : 131071*((U-C : ℕ) : ℤ) ≤ V-K := by
    dsimp [C, K]
    omega
  have hA : 131071*((T-U : ℕ) : ℤ) ≤ 131071*T-V+131071 := by omega
  have hm := boxPoly_mono 131071
    (131071*((T-U : ℕ) : ℤ)) (131071*((U-C : ℕ) : ℤ)) (131071*C)
    (131071*T-V+131071) (V-K) K (by norm_num) (by positivity)
    (by positivity) (by positivity) hA hB hK
  rw [boxPoly_scaled, ← channel_poly] at hm
  convert hm using 1 <;> push_cast <;> ring

structure Affine where
  constant : ℤ
  slope : ℤ
  deriving DecidableEq, Repr

def Affine.eval (a : Affine) (i : ℕ) : ℤ := a.constant+a.slope*i

def triplePrefix (a b c : Affine) (n : ℕ) : ℤ :=
  let x : ℤ := n
  12*x*(a.constant*b.constant*c.constant)+
  6*x*(x-1)*(a.slope*b.constant*c.constant+a.constant*b.slope*c.constant+a.constant*b.constant*c.slope)+
  2*x*(x-1)*(2*x-1)*(a.slope*b.slope*c.constant+a.slope*b.constant*c.slope+a.constant*b.slope*c.slope)+
  3*x*x*(x-1)*(x-1)*(a.slope*b.slope*c.slope)

theorem triplePrefix_eq (a b c : Affine) (n : ℕ) :
    triplePrefix a b c n = 12*∑ i ∈ Finset.range n, a.eval i*b.eval i*c.eval i := by
  induction n with
  | zero => simp [triplePrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ← ih]
      simp only [triplePrefix, Affine.eval, Nat.cast_add, Nat.cast_one]
      ring


def Affine.add (a b : Affine) : Affine := ⟨a.constant+b.constant,a.slope+b.slope⟩
def Affine.sub (a b : Affine) : Affine := ⟨a.constant-b.constant,a.slope-b.slope⟩
def Affine.scale (a : Affine) (k : ℤ) : Affine := ⟨k*a.constant,k*a.slope⟩
def Affine.plus (a : Affine) (k : ℤ) : Affine := ⟨a.constant+k,a.slope⟩

@[simp] theorem Affine.eval_add (a b : Affine) (i : ℕ) :
    (a.add b).eval i = a.eval i+b.eval i := by simp [Affine.add, Affine.eval]; ring
@[simp] theorem Affine.eval_sub (a b : Affine) (i : ℕ) :
    (a.sub b).eval i = a.eval i-b.eval i := by simp [Affine.sub, Affine.eval]; ring
@[simp] theorem Affine.eval_scale (a : Affine) (k : ℤ) (i : ℕ) :
    (a.scale k).eval i = k*a.eval i := by simp [Affine.scale, Affine.eval]; ring
@[simp] theorem Affine.eval_plus (a : Affine) (k : ℤ) (i : ℕ) :
    (a.plus k).eval i = a.eval i+k := by simp [Affine.plus, Affine.eval]; ring

def boxPrefix (a b c : Affine) (n : ℕ) : ℤ :=
  3*triplePrefix (c.plus 131071) (a.plus 131071) (c.plus (2*131071)) n+
  triplePrefix (c.plus 131071) c (c.plus (2*131071)) n+
  6*triplePrefix (c.plus 131071) a b n+
  9*131071*triplePrefix (c.plus 131071) b ⟨1,0⟩ n+
  3*triplePrefix (c.plus 131071) b c n+
  3*triplePrefix (c.plus 131071) b b n

def factoredBoxPrefix (a b c : Affine) (n : ℕ) : ℤ :=
  if n = 0 then 0 else
  let x : ℤ := n
  let w : ℤ := 131071
  let A := a.constant
  let B := b.constant
  let C := c.constant
  let α := a.slope
  let β := b.slope
  let γ := c.slope
  let q0 := 3*(A+w)*(C+2*w)+C*(C+2*w)+6*A*B+9*w*B+3*B*C+3*B*B
  let q1 := 3*((A+w)*γ+α*(C+2*w))+γ*(2*C+2*w)+
    6*(A*β+α*B)+9*w*β+3*(B*γ+β*C)+6*B*β
  let q2 := 3*α*γ+γ*γ+6*α*β+3*β*γ+3*β*β
  let s0 := 12*x
  let s1 := 6*x*(x-1)
  let s2 := 2*x*(x-1)*(2*x-1)
  let s3 := 3*x*x*(x-1)*(x-1)
  q0*(s0*(C+w)+s1*γ)+q1*(s1*(C+w)+s2*γ)+q2*(s2*(C+w)+s3*γ)

theorem factoredBoxPrefix_eq (a b c : Affine) (n : ℕ) :
    factoredBoxPrefix a b c n = boxPrefix a b c n := by
  unfold factoredBoxPrefix
  split_ifs with hn
  · subst n
    simp [boxPrefix, triplePrefix]
  · simp only [boxPrefix, triplePrefix, Affine.plus]
    ring

theorem boxPrefix_eq (a b c : Affine) (n : ℕ) :
    boxPrefix a b c n =
      12*∑ i ∈ Finset.range n, boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by
  simp only [boxPrefix, triplePrefix_eq, Affine.eval_plus]
  apply Eq.symm
  calc
    _ = ∑ i ∈ Finset.range n, 12*boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range n,
        ((3*(12*((c.eval i+131071)*(a.eval i+131071)*(c.eval i+2*131071))))+
        (12*((c.eval i+131071)*c.eval i*(c.eval i+2*131071)))+
        (6*(12*((c.eval i+131071)*a.eval i*b.eval i)))+
        (9*131071*(12*((c.eval i+131071)*b.eval i*(Affine.eval ⟨1,0⟩ i))))+
        (3*(12*((c.eval i+131071)*b.eval i*c.eval i)))+
        (3*(12*((c.eval i+131071)*b.eval i*b.eval i)))) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [boxPoly, Affine.eval]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem boxPrefix_interval (a b c : Affine) (lo hi : ℕ) (h : lo ≤ hi) :
    boxPrefix a b c hi-boxPrefix a b c lo =
      12*∑ i ∈ Finset.Ico lo hi, boxPoly 131071 (a.eval i) (b.eval i) (c.eval i) := by
  rw [boxPrefix_eq, boxPrefix_eq]
  rw [← Finset.sum_range_add_sum_Ico _ h]
  ring

theorem Affine.nonneg_between (a : Affine) (lo hi i : ℕ)
    (hlo : lo ≤ i) (hhi : i ≤ hi) (h0 : 0 ≤ a.eval lo) (h1 : 0 ≤ a.eval hi) :
    0 ≤ a.eval i := by
  unfold Affine.eval at *
  rcases le_total 0 a.slope with hs | hs
  · have hh := mul_le_mul_of_nonneg_left (show (lo : ℤ) ≤ i by omega) hs
    omega
  · have hh := mul_le_mul_of_nonpos_left (show (i : ℤ) ≤ hi by omega) hs
    omega

end ProximityPrize.SubmissionLower.Lower80889.BandPolynomial

namespace ProximityPrize.SubmissionLower.Lower80889.CompressedBand
open scoped BigOperators
open Lower80889.BandPolynomial Lower80889.ThresholdIndexed
open Lower80889.ThresholdFast LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

structure Input where
  T : ℕ
  YS : ℕ
  S : ℕ
  Dh : ℕ
  dT : ℕ
  dY : ℕ
  dS : ℕ
  dDh : ℕ
  fuel : ℕ
  deriving DecidableEq, Repr

def Input.atT (p : Input) : Affine := ⟨p.T,-(p.dT : ℤ)⟩
def Input.atY (p : Input) : Affine := ⟨p.YS,-(p.dY : ℤ)⟩
def Input.atS (p : Input) : Affine := ⟨p.S,-(p.dS : ℤ)⟩
def Input.atDh (p : Input) : Affine := ⟨p.Dh,-(p.dDh : ℤ)⟩
def Input.count (p : Input) (i : ℕ) : ℕ :=
  channelCount (p.T-i*p.dT)
    (min (p.YS-i*p.dY) ((p.Dh-i*p.dDh+(p.S-i*p.dS)-1)/131071)) (p.S-i*p.dS)

def Input.dh (p : Input) (code : ℕ) : Affine := if 6 ≤ code then p.atDh else ⟨0,0⟩
def Input.u (p : Input) (code : ℕ) : Affine :=
  if code/2%3 = 0 then p.atT.scale 131071
  else if code/2%3 = 1 then p.atY.scale 131071
  else (p.dh code).add p.atS
def Input.c (p : Input) (code : ℕ) : Affine :=
  if code%2 = 0 then p.atS.scale 131071 else p.u code
def Input.a (p : Input) (code : ℕ) : Affine := ((p.atT.scale 131071).sub (p.u code)).plus 131071
def Input.b (p : Input) (code : ℕ) : Affine := (p.u code).sub (p.c code)

def conditions (p : Input) (code : ℕ) : List Affine :=
  [p.atT,p.atY,p.atS,if 6 ≤ code then p.atDh else p.atDh.scale (-1),
    (p.atT.scale 131071).sub (p.u code),
    (p.atY.scale 131071).sub (p.u code),
    ((p.dh code).add p.atS).sub (p.u code),
    (p.atS.scale 131071).sub (p.c code),
    (p.u code).sub (p.c code)]

def ValidAt (p : Input) (code i : ℕ) : Prop :=
  ∀ a ∈ conditions p code, 0 ≤ a.eval i
def FastValidAt (p : Input) (code i : ℕ) : Prop :=
  let t := p.atT.eval i
  let y := p.atY.eval i
  let s := p.atS.eval i
  let u := (p.u code).eval i
  let c := (p.c code).eval i
  0 ≤ t ∧ 0 ≤ y ∧ 0 ≤ s ∧
    0 ≤ (if 6 ≤ code then p.atDh else p.atDh.scale (-1)).eval i ∧
    u ≤ 131071*t ∧ u ≤ 131071*y ∧ u ≤ (p.dh code).eval i+s ∧
    c ≤ 131071*s ∧ c ≤ u
instance  _root_.ProximityPrize.SubmissionLower.Lower80889.CompressedBand.instDecidableFastValidAt (p : Input) (code i : ℕ) : Decidable (FastValidAt p code i) := by
  unfold FastValidAt
  infer_instance

theorem validAt_iff_fast (p : Input) (code i : ℕ) :
    ValidAt p code i ↔ FastValidAt p code i := by
  simp only [ValidAt, FastValidAt, conditions, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Affine.eval_sub, Affine.eval_scale, Affine.eval_add, sub_nonneg]

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.CompressedBand.instDecidableValidAt (p : Input) (code i : ℕ) : Decidable (ValidAt p code i) :=
  decidable_of_iff (FastValidAt p code i) (validAt_iff_fast p code i).symm

theorem validAt_between (p : Input) (code lo hi i : ℕ)
    (hlo : lo ≤ i) (hhi : i ≤ hi) (h0 : ValidAt p code lo) (h1 : ValidAt p code hi) :
    ValidAt p code i := by
  intro a ha
  exact a.nonneg_between lo hi i hlo hhi (h0 a ha) (h1 a ha)

theorem linear_cast (t d i : ℕ) (h : 0 ≤ Affine.eval ⟨t,-(d : ℤ)⟩ i) :
    ((t-i*d : ℕ) : ℤ) = Affine.eval ⟨t,-(d : ℤ)⟩ i := by
  simp only [Affine.eval, neg_mul] at *
  have hc : ((i*d : ℕ) : ℤ) = (d : ℤ)*i := by push_cast; ring
  omega

theorem validAt_bound (p : Input) (code i : ℕ) (h : ValidAt p code i) :
    6*131071^3*(p.count i : ℤ) ≤
      boxPoly 131071 ((p.a code).eval i) ((p.b code).eval i) ((p.c code).eval i) := by
  simp only [ValidAt, conditions, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h
  rcases h with ⟨hT,hY,hS,hD,hU0,hU1,hU2,hC0,hC1⟩
  have htc := linear_cast p.T p.dT i hT
  have hyc := linear_cast p.YS p.dY i hY
  have hsc := linear_cast p.S p.dS i hS
  change ((p.T-i*p.dT : ℕ) : ℤ) = p.atT.eval i at htc
  change ((p.YS-i*p.dY : ℕ) : ℤ) = p.atY.eval i at hyc
  change ((p.S-i*p.dS : ℕ) : ℤ) = p.atS.eval i at hsc
  have hdc : ((p.Dh-i*p.dDh : ℕ) : ℤ) = (p.dh code).eval i := by
    unfold Input.dh
    split_ifs with hd
    · simp only [hd, ↓reduceIte] at hD
      exact linear_cast p.Dh p.dDh i hD
    · simp only [hd, ↓reduceIte, Affine.eval_scale] at hD
      simp only [Input.atDh, Affine.eval, neg_mul] at hD ⊢
      have hc : ((i*p.dDh : ℕ) : ℤ) = (p.dDh : ℤ)*i := by push_cast; ring
      omega
  simp only [Affine.eval_sub, Affine.eval_scale, Affine.eval_add] at hU0 hU1 hU2 hC0 hC1
  have hue : (p.u code).eval i =
      min (131071*p.atT.eval i) (min (131071*p.atY.eval i) ((p.dh code).eval i+p.atS.eval i)) := by
    by_cases h0 : code/2%3 = 0
    · simp only [Input.u, h0, ↓reduceIte, Affine.eval_scale] at hU0 hU1 hU2 ⊢
      omega
    · by_cases h1 : code/2%3 = 1
      · simp only [Input.u, h0, h1, Nat.one_ne_zero, ↓reduceIte, Affine.eval_scale] at hU0 hU1 hU2 ⊢
        omega
      · simp only [Input.u, h0, h1, Nat.one_ne_zero, ↓reduceIte, Affine.eval_add] at hU0 hU1 hU2 ⊢
        omega
  have hce : (p.c code).eval i = min (131071*p.atS.eval i) ((p.u code).eval i) := by
    by_cases h0 : code%2 = 0 <;>
      simp only [Input.c, h0, ↓reduceIte, Affine.eval_scale] at hC0 hC1 ⊢ <;> omega
  have hb := channel_thin_bound (p.T-i*p.dT) (p.YS-i*p.dY) (p.S-i*p.dS) (p.Dh-i*p.dDh)
  push_cast at hb
  rw [htc,hyc,hsc,hdc,← hue,← hce] at hb
  norm_num only [Int.reducePow, Int.reduceMul]
  simpa only [Input.count,Input.a,Input.b,Affine.eval_plus,Affine.eval_sub,Affine.eval_scale] using hb



def RunValid (p : Input) (start : ℕ) (run : Run) : Prop :=
  start < run.stop ∧ run.stop ≤ p.fuel ∧
    ValidAt p run.code start ∧ ValidAt p run.code (run.stop-1)
instance  _root_.ProximityPrize.SubmissionLower.Lower80889.CompressedBand.instDecidableRunValid (p : Input) (start : ℕ) (run : Run) : Decidable (RunValid p start run) := by
  unfold RunValid; infer_instance

def runUpper (p : Input) (start : ℕ) (run : Run) : ℤ :=
  factoredBoxPrefix (p.a run.code) (p.b run.code) (p.c run.code) run.stop-
  factoredBoxPrefix (p.a run.code) (p.b run.code) (p.c run.code) start

theorem runValid_bound (p : Input) (start : ℕ) (run : Run)
    (h : RunValid p start run) :
    72*131071^3*(∑ i ∈ Finset.Ico start run.stop, (p.count i : ℤ)) ≤ runUpper p start run := by
  rw [runUpper, factoredBoxPrefix_eq, factoredBoxPrefix_eq, boxPrefix_interval _ _ _ _ _ h.1.le]
  have hs : (∑ i ∈ Finset.Ico start run.stop, 6*131071^3*(p.count i : ℤ)) ≤
      ∑ i ∈ Finset.Ico start run.stop,
        boxPoly 131071 ((p.a run.code).eval i) ((p.b run.code).eval i) ((p.c run.code).eval i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact validAt_bound p run.code i (validAt_between p run.code start (run.stop-1) i
      (Finset.mem_Ico.mp hi).1 (by have := (Finset.mem_Ico.mp hi).2; omega) h.2.2.1 h.2.2.2)
  rw [← Finset.mul_sum] at hs
  linarith

def RunsValid (p : Input) : ℕ → List Run → Prop
  | start, [] => start = p.fuel
  | start, run::runs => RunValid p start run ∧ RunsValid p run.stop runs
instance  _root_.ProximityPrize.SubmissionLower.Lower80889.CompressedBand.instDecidableRunsValid (p : Input) (start : ℕ) (runs : List Run) : Decidable (RunsValid p start runs) := by
  induction runs generalizing start with
  | nil => unfold RunsValid; infer_instance
  | cons run runs ih => unfold RunsValid; infer_instance

def runsUpper (p : Input) : ℕ → List Run → ℤ
  | _, [] => 0
  | start, run::runs => runUpper p start run+runsUpper p run.stop runs

theorem runsValid_bound (p : Input) (start : ℕ) (runs : List Run)
    (h : RunsValid p start runs) :
    72*131071^3*(∑ i ∈ Finset.Ico start p.fuel, (p.count i : ℤ)) ≤ runsUpper p start runs := by
  induction runs generalizing start with
  | nil => simp only [RunsValid] at h; simp [h, runsUpper]
  | cons run runs ih =>
      have h0 := runValid_bound p start run h.1
      have h1 := ih run.stop h.2
      rw [← Finset.sum_Ico_consecutive _ h.1.1.le h.1.2.1]
      simp only [runsUpper]
      linarith


open Lower80889.Oracle LocatorArbitraryPowerAvoidance
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (rawFlag)

def ofSource (s : SourceNumbers) (p : FlagDegree) : Input :=
  ⟨s.totalCap-total p,s.middleCap-middle p,s.slopeCap-p.all,s.contactCap p,
    total p,middle p,p.all,50185+contactDec p,s.fuel p⟩

theorem indexed_sum (p : Input) (dc n : ℕ) (hd : p.dDh = 50185+dc) :
    (indexedThin 131071 p.Dh 50185 dc p.dT p.dY p.dS p.T p.YS p.S n : ℤ) =
      50185*∑ i ∈ Finset.range n, (p.count i : ℤ) := by
  induction n with
  | zero => simp [indexedThin]
  | succ n ih =>
      rw [indexedThin, Nat.cast_add, Nat.cast_mul, ih, Finset.sum_range_succ]
      simp only [Input.count, channelCount_eq_eval, thinTop, hd]
      push_cast
      ring

theorem source_sum (s : SourceNumbers) (p : FlagDegree) :
    (indexedBand s p : ℤ) =
      50185*∑ i ∈ Finset.range (ofSource s p).fuel, ((ofSource s p).count i : ℤ) :=
  indexed_sum (ofSource s p) (contactDec p) (s.fuel p) rfl

def Sufficient (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) : Prop :=
  10714-(r+v) < threshold ∨
    let p := rawFlag r v threshold
    1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧ p.all ≤ s.slopeCap ∧
      RunsValid (ofSource s p) 0 runs ∧
      50185*runsUpper (ofSource s p) 0 runs < (s.gap : ℤ)*(72*131071^3)
instance  _root_.ProximityPrize.SubmissionLower.Lower80889.CompressedBand.instDecidableSufficient (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run) :
    Decidable (Sufficient s r v threshold runs) := by
  unfold Sufficient; infer_instance

theorem sufficient_sound (s : SourceNumbers) (r v threshold : ℕ) (runs : List Run)
    (h : Sufficient s r v threshold runs) : FastSourceThresholdSufficient s r v threshold := by
  rcases h with h | ⟨hr,ht,hy,hs,hvalid,hgap⟩
  · exact Or.inl h
  apply sufficient_of_indexed
  refine Or.inr ⟨hr,ht,hy,hs,?_⟩
  have hb := runsValid_bound (ofSource s (rawFlag r v threshold)) 0 runs hvalid
  rw [Nat.Ico_zero_eq_range] at hb
  have he := source_sum s (rawFlag r v threshold)
  have hi : (indexedBand s (rawFlag r v threshold) : ℤ) < s.gap := by
    nlinarith only [hgap, congrArg (fun x : ℤ => (72*131071^3)*x) he,
      mul_le_mul_of_nonneg_left hb (show (0 : ℤ) ≤ 50185 by norm_num)]
  exact_mod_cast hi

end ProximityPrize.SubmissionLower.Lower80889.CompressedBand


