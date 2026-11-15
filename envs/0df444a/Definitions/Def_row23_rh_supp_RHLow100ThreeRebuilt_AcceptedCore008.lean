-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore008
-- name    : row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore008
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:18:08.891533+00:00
-- url     : https://prove2.me/theorems/ccb3a2da-1f4b-40e1-9dd0-43d8be3fa78f
-- title:
--   Row 23 RH support: RHLow100ThreeRebuilt.AcceptedCore008
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThreeRebuilt_AcceptedCore007
/-
Compact certificate adaptation of sometik179's height-14–100 proof,
Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03).
The theta/Mellin attribution to Gabewhigham is retained in the source.
Large records are reconstructed by ordinary Lean definitions. The original
kernel validators still establish every numerical certificate condition.
-/
import Definitions.Def_row23_rh_supp_RHLow100ThetaReplacement
import Theorems.Thm_TaoFivePrimes_rh14to100_moments_enclosed
import Definitions.Def_row23_rh_supp_RHLow100TranslationReplacement
import Definitions.Def_row23_rh_supp_RHLow100BernsteinReplacement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.GCongr

/- Ordinary finite arithmetic definitions extracted from sometik179's
height-14–100 certificate, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a.
Theta/Mellin attribution to Gabewhigham is retained. No certificate assertion
or RH theorem is supplied in this definition interface. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false


/- Source module: ThetaPointModel. -/
section Height100Module40

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option exponentiation.threshold 1024

namespace CertifiedThetaPoints
open CertifiedFixedPoint CertifiedHighPrecisionPi

noncomputable def quarterExpBox (i : Fin 16) : Box := repeatedSquare scale310 1 (cachedPointExp i)
noncomputable def lambda (i : Fin 16) (n : Fin 8) : ℝ :=
  Real.pi*(n.val+1:ℝ)^2*Real.exp (center i)

noncomputable instance (i : Fin 16) (n : Fin 8) : Decidable (active i n) := inferInstanceAs
  (Decidable ((lambdaBox i n).lo < 800*scale310))

lemma piBox_sound : Contains scale310 piBox Real.pi := by
  simpa only [Contains,piBox,scale310,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using pi_enclosure_310

lemma centerExpBox_sound (i : Fin 16) :
    Contains scale310 (centerExpBox i) (Real.exp (center i)) := by
  have h := repeatedSquare_sound (by norm_num [scale310] : 0< scale310) 3 (pointExp_sound i)
  have he : (Real.exp (center i/8))^(2^3)=Real.exp (center i) := by
    rw [←Real.exp_nat_mul]
    norm_num
    ring
  simpa only [centerExpBox,he] using h

lemma quarterExpBox_sound (i : Fin 16) :
    Contains scale310 (quarterExpBox i) (Real.exp (center i/4)) := by
  have h := repeatedSquare_sound (by norm_num [scale310] : 0< scale310) 1 (pointExp_sound i)
  have he : (Real.exp (center i/8))^(2^1)=Real.exp (center i/4) := by
    rw [←Real.exp_nat_mul]
    norm_num
    ring
  simpa only [quarterExpBox,he] using h

lemma lambdaBox_sound (i : Fin 16) (n : Fin 8) :
    Contains scale310 (lambdaBox i n) (lambda i n) := by
  have h := scaleBox_sound ((n.val+1)^2)
    (mulDivBox_sound (by norm_num [scale310] : 0< scale310) (by decide : 0<1)
      piBox_sound (centerExpBox_sound i))
  simpa [lambdaBox,lambda,mul_comm,mul_left_comm,mul_assoc] using h

lemma active_bound_check : ∀ i : Fin 16, ∀ n : Fin 8,
    active i n → (lambdaBox i n).hi ≤  1024*scale310 := by decide +kernel

lemma active_lambda_le (i : Fin 16) (n : Fin 8) (h : active i n) : lambda i n≤ 1024 := by
  have hb := (lambdaBox_sound i n).2
  have hc := active_bound_check i n h
  have hSr : (0:ℝ)< scale310 := by norm_num [scale310]
  have he : ((lambdaBox i n).hi:ℝ)/scale310 ≤  1024 := by
    apply (div_le_iff₀ hSr).mpr
    exact_mod_cast hc
  exact hb.trans he

lemma inactive_lambda_ge (i : Fin 16) (n : Fin 8) (h : ¬active i n) : 800≤ lambda i n := by
  have hb := (lambdaBox_sound i n).1
  have hc : 800*scale310 ≤  (lambdaBox i n).lo := Nat.le_of_not_gt h
  have hSr : (0:ℝ)< scale310 := by norm_num [scale310]
  have he : (800:ℝ) ≤  ((lambdaBox i n).lo:ℝ)/scale310 := by
    apply (le_div_iff₀ hSr).mpr
    exact_mod_cast hc
  exact he.trans hb

noncomputable def thetaInitialBox (i : Fin 16) (n : Fin 8) : Box :=
  if active i n then expNegative310 (lambdaBox i n) else ⟨0,0⟩

noncomputable def fullInitialBox (i : Fin 16) (n : Fin 8) : Box :=
  scaleBox 2 (mulDivBox scale310 1 (quarterExpBox i) (thetaInitialBox i n))

lemma thetaInitialBox_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (thetaInitialBox i n) (Real.exp (-lambda i n)) := by
  rw [thetaInitialBox,if_pos h]
  exact expNegative310_sound (lambdaBox_sound i n) (active_lambda_le i n h)

lemma fullInitialBox_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (fullInitialBox i n) (2*Real.exp (center i/4-lambda i n)) := by
  have he := mulDivBox_sound (by norm_num [scale310] : 0< scale310) (by decide : 0<1)
    (quarterExpBox_sound i) (thetaInitialBox_sound i n h)
  have hs := scaleBox_sound 2 he
  simpa [fullInitialBox,←Real.exp_add,sub_eq_add_neg] using hs

end CertifiedThetaPoints

end Height100Module40

/- Source module: ThetaInitialCertificate. -/
section Height100Module41

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertifiedThetaPoints
open CertifiedFixedPoint

noncomputable def initialValues : List (List Box) := List.ofFn (fun i : Fin 16 => List.ofFn (fullInitialBox i))

theorem _root_.CertifiedThetaPoints.initialCache_correct : CertifiedThetaPoints.initialValues = CertifiedThetaPoints.initialCache :=
  Eq.refl CertifiedThetaPoints.initialCache

lemma cachedInitial_eq (i : Fin 16) (n : Fin 8) : cachedInitial i n=fullInitialBox i n := by
  rw [cachedInitial,←initialCache_correct]
  simp only [initialValues,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos i.isLt,dif_pos n.isLt,Option.getD_some]

lemma cachedInitial_sound (i : Fin 16) (n : Fin 8) (h : active i n) :
    Contains scale310 (cachedInitial i n) (2*Real.exp (center i/4-lambda i n)) := by
  rw [cachedInitial_eq]
  exact fullInitialBox_sound i n h

end CertifiedThetaPoints

end Height100Module41

/- Source module: JetCandidate. -/
section Height100Module42

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CertifiedThetaCandidates
open CertifiedThetaPoints CertifiedFixedPoint

structure Candidate where
  lambdaLo : Array ℕ
  lambdaHi : Array ℕ
  g : Array ℤ
  r : Array ℕ
  f : Array ℤ
  s : Array ℕ
  deriving Repr

/-- This is only a candidate generator. Every result must separately satisfy the
kernel-checked integer enclosure and ODE residual conditions. -/
noncomputable def propose (i : Fin 16) (n : Fin 8) (N : ℕ := 184) : Candidate := Id.run do
  let lam := lambdaBox i n
  let mut l := lam.lo
  let mut u := lam.hi
  let mut ls := #[]
  let mut us := #[]
  let mut gs := #[]
  let mut rs := #[]
  for j in List.range N do
    if j>0 then
      l := 3*l/(16*j)
      u := 3*u/(16*j)+1
    ls := ls.push l
    us := us.push u
    let offset := if j=0 then scale310*(6*i.val+3)/64 else if j=1 then scale310*3/64 else 0
    gs := gs.push ((offset:ℤ)-(l:ℤ))
    rs := rs.push (u-l+1)
  let initial := cachedInitial i n
  let mut fs := #[(initial.lo:ℤ)]
  let mut ss := #[initial.hi-initial.lo]
  for j in (List.range (N-1)).map (·+1) do
    let mut v : ℤ := 0
    let mut e : ℕ := 0
    for k in (List.range j).map (·+1) do
      let g := gs[k]?.getD 0
      let r := rs[k]?.getD 0
      let f := fs[j-k]?.getD 0
      let s := ss[j-k]?.getD 0
      v := v+(k:ℤ)*g*f
      e := e+k*(g.natAbs*s+r*f.natAbs+r*s)
    let denominator := scale310*j
    let c := v/(denominator:ℤ)
    let residual := ((denominator:ℤ)*c-v).natAbs
    fs := fs.push c
    ss := ss.push ((residual+e)/denominator+1)
  return ⟨ls,us,gs,rs,fs,ss⟩

end CertifiedThetaCandidates

end Height100Module42

/- Source module: StreamingODECheck. -/
section Height100Module43

namespace CertifiedStreamingODE
open CertifiedSignedODEConvolution

lemma digit_shift (bits p j : ℕ) : digit bits (p>>>bits) j=digit bits p (j+1) := by
  unfold digit
  rw [←Nat.shiftRight_add]
  congr 2
  simp [Nat.mul_add,add_comm]

lemma tail_getD {α : Type*} (xs : List α) (j : ℕ) (d : α) :
    xs.tail.getD j d=xs.getD (j+1) d := by
  cases xs <;> simp

/-- The streaming checker verifies each coefficient inequality while consuming
each list and each packed integer exactly once. -/
theorem checkSteps_sound (bits D i n : ℕ) (fs : List ℤ) (ss : List ℕ)
    (pp pm pe pr : ℕ) (hc : checkSteps bits D i n fs ss pp pm pe pr=true) :
    ∀ j< n,
      (((i+j+1:ℕ):ℤ)*fs.getD j 0*D+(digit bits pp j:ℤ)-(digit bits pm j:ℤ)).natAbs+
        digit bits pe j+digit bits pr j≤ (i+j+1)*ss.getD j 0*D := by
  induction n generalizing i fs ss pp pm pe pr with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [checkSteps,Bool.and_eq_true,decide_eq_true_eq] at hc
    obtain ⟨hhead,htail⟩ := hc
    intro j hj
    cases j with
    | zero =>
      simpa only [digit,Nat.mul_zero,Nat.shiftRight_zero,Nat.add_zero,Nat.cast_add,
        Nat.cast_one,Int.natCast_emod,Nat.cast_pow,Nat.cast_ofNat,List.headD_eq_getD] using hhead
    | succ j =>
      have h := ih (i+1) fs.tail ss.tail (pp>>>bits) (pm>>>bits) (pe>>>bits) (pr>>>bits)
        htail j (by omega)
      simpa only [digit_shift,tail_getD,Nat.succ_eq_add_one,add_assoc,add_left_comm] using h

end CertifiedStreamingODE

end Height100Module43

/- Source module: JetRecordData. -/
section Height100Module44

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CertifiedJetRecords
open CertifiedThetaCandidates CertifiedThetaPoints CertifiedFixedPoint
open CertifiedListODEVectors CertifiedPackedConvolution CertifiedStreamingODE

noncomputable def makeRecord (i : Fin 16) (n : Fin 8) : Record :=
  if active i n then
    let d := propose i n
    let entries := List.ofFn (fun j : Fin 184 =>
      Entry.mk (d.lambdaLo[j.val]?.getD 0) (d.lambdaHi[j.val]?.getD 0)
        (d.g[j.val]?.getD 0) (d.r[j.val]?.getD 0)
        (d.f[j.val]?.getD 0) (d.s[j.val]?.getD 0))
    let r : Record := ⟨entries,0,0,0,0⟩
    ⟨entries, lowProduct r.ad r.fp, lowProduct r.ad r.fm,
      lowProduct r.ad r.ss, lowProduct r.rd r.fr⟩
  else ⟨[],0,0,0,0⟩

end CertifiedJetRecords

end Height100Module44

/- Source module: JetRecordCertificateNoCode. -/
section Height100Module45
namespace CertifiedJetRecords
theorem records_checked (i : Fin 16) (n : Fin 8)
    (ha : CertifiedThetaPoints.active i n) : checkRecord i n (recordAt i n)=true :=
  TaoFivePrimes.rh14to100_theta_checks i n ha
end CertifiedJetRecords
end Height100Module45

/- Source module: JetRecordCertificate. -/
section Height100Module46

end Height100Module46

/- Source module: JetInputCheck. -/
section Height100Module47

namespace CertifiedJetRecords

lemma checkInputs_head (D p limit j : ℕ) (e : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::es)=true) : entryCondition D p limit j e := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  exact of_decide_eq_true h

lemma checkInputs_tail (D p limit j : ℕ) (e : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::es)=true) : checkInputs D p limit (j+1) es=true :=
  (Bool.and_eq_true_iff.mp hc).2

lemma checkInputs_next (D p limit j : ℕ) (e f : Entry) (es : List Entry)
    (hc : checkInputs D p limit j (e::f::es)=true) : nextCondition j e f := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  exact of_decide_eq_true h

theorem checkInputs_entry (D p limit j : ℕ) (es : List Entry)
    (hc : checkInputs D p limit j es=true) :
    ∀ k< es.length, entryCondition D p limit (j+k) (es.getD k zeroEntry) := by
  induction es generalizing j with
  | nil => intro k hk; simp at hk
  | cons e es ih =>
    intro k hk
    cases k with
    | zero => simpa using checkInputs_head D p limit j e es hc
    | succ k =>
      have h := ih (j+1) (checkInputs_tail D p limit j e es hc) k (by simpa using hk)
      change entryCondition D p limit (j+(k+1)) (es.getD k zeroEntry)
      simpa only [add_assoc,add_comm,add_left_comm] using h

theorem checkInputs_adjacent (D p limit j : ℕ) (es : List Entry)
    (hc : checkInputs D p limit j es=true) :
    ∀ k, k+1< es.length → nextCondition (j+k) (es.getD k zeroEntry) (es.getD (k+1) zeroEntry) := by
  induction es generalizing j with
  | nil => intro k hk; simp at hk
  | cons e es ih =>
    intro k hk
    cases k with
    | zero =>
      cases es with
      | nil => simp at hk
      | cons f es => simpa using checkInputs_next D p limit j e f es hc
    | succ k =>
      have h := ih (j+1) (checkInputs_tail D p limit j e es hc) k (by simpa using hk)
      change nextCondition (j+(k+1)) (es.getD k zeroEntry) (es.getD (k+1) zeroEntry)
      simpa only [add_assoc,add_comm,add_left_comm] using h

end CertifiedJetRecords

end Height100Module47

/- Source module: JetRecordODE. -/
section Height100Module48

set_option autoImplicit false
namespace CertifiedJetRecords
open CertifiedFixedPoint CertifiedThetaPoints CertifiedSignedODEConvolution
open CertifiedListODEVectors CertifiedStreamingODE CertifiedIntegerExponentialJets

noncomputable def Record.G (d : Record) (j : ℕ) : ℤ := d.gs.getD j 0
noncomputable def Record.F (d : Record) (j : ℕ) : ℤ := d.fs.getD j 0
noncomputable def Record.R (d : Record) (j : ℕ) : ℕ := d.rs.getD j 0
noncomputable def Record.S (d : Record) (j : ℕ) : ℕ := d.ss.getD j 0

theorem checkRecord_conditions (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) :
    initialCondition i n d ∧ checkInputs scale310 i.val (10^75) 0 d.entries=true ∧
    d.gs.tail.all (fun g => decide (g≤ 0))=true ∧ carryCondition d ∧ productCondition d ∧
    checkSteps bits scale310 0 (precision-1) d.fs.tail d.ss.tail d.pp d.pm d.pe d.pr=true := by
  simpa only [checkRecord,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc

theorem checked_record_ode (i : Fin 16) (n : Fin 8) (d : Record)
    (hc : checkRecord i n d=true) (j : ℕ) (hj : j+1<184) :
    |integerResidual scale310 d.G d.F j|+integerErrorSum d.G d.F d.R d.S j ≤ 
      (j+1:ℤ)*d.S (j+1)*scale310 := by
  obtain ⟨_hi,_hin,hsign,hcarry,hprod,hstream⟩ := checkRecord_conditions i n d hc
  obtain ⟨hcp,hcm,hce,hcr⟩ := hcarry
  obtain ⟨hpp,hpm,hpe,hpr⟩ := hprod
  have hj' : j< precision-1 := by dsimp [precision]; omega
  have hlen : d.fs.length=d.ss.length := by simp [Record.fs,Record.ss]
  have hp : digit bits d.pp j=conv (absDerivative d.G) (positive d.F) j := by
    rw [hpp,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcp
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      simp only [Record.fp,positiveList_getD,positive,Record.F]
  have hm : digit bits d.pm j=conv (absDerivative d.G) (negative d.F) j := by
    rw [hpm,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcm
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      simp only [Record.fm,negativeList_getD,negative,Record.F]
  have he : digit bits d.pe j=conv (absDerivative d.G) d.S j := by
    rw [hpe,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hce
    · intro k hk
      simp only [Record.ad,absDerivativeList_getD,absDerivative,Record.G]
    · intro k hk
      rfl
  have hr : digit bits d.pr j=conv (radiusDerivative d.R) (fun k => (d.F k).natAbs+d.S k) j := by
    rw [hpr,lowProduct,Nat.shiftLeft_eq',Nat.shiftLeft_eq,one_mul,digit_truncate bits _ _ j hj']
    apply digit_lists _ _ _ _ _ _ _ _ hcr
    · intro k hk
      simp only [Record.rd,radiusDerivativeList_getD,radiusDerivative,Record.R]
    · intro k hk
      simp only [Record.fr,radiusFactorList_getD _ _ hlen,Record.F,Record.S]
  have hneg : ∀ k, k≤ j → d.G (k+1)≤ 0 := by
    intro k hk
    have hh := list_all_nonpos d.gs.tail hsign k
    simpa only [CertifiedListODEVectors.getD_tail,Record.G] using hh
  apply residual_check_of_convolutions scale310 d.G d.F d.R d.S j
    (digit bits d.pp j) (digit bits d.pm j) (digit bits d.pe j) (digit bits d.pr j)
    hneg hp hm he hr
  have hh := checkSteps_sound bits scale310 0 (precision-1) d.fs.tail d.ss.tail
    d.pp d.pm d.pe d.pr hstream j hj'
  simpa only [zero_add,Nat.cast_add,Nat.cast_one,CertifiedStreamingODE.tail_getD,Record.F,Record.S] using hh

end CertifiedJetRecords

end Height100Module48

/- Source module: RationalJetIntervals. -/
section Height100Module49

set_option autoImplicit false
namespace CertifiedFixedPoint

lemma rationalStep_sound {S d : ℕ} (hS : 0< S) (hd : 0< d) (p : ℕ)
    {a b : Box} {x : ℝ} (ha : Contains S a x)
    (hl : b.lo*d≤ p*a.lo) (hh : p*a.hi≤ b.hi*d) :
    Contains S b ((p:ℝ)*x/d) := by
  have hSr : (0:ℝ)< S := by exact_mod_cast hS
  have hdr : (0:ℝ)< d := by exact_mod_cast hd
  have hlr : (b.lo:ℝ)≤ (p:ℝ)*a.lo/d := by
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast hl
  have hhr : (p:ℝ)*a.hi/d≤ (b.hi:ℝ) := by
    apply (div_le_iff₀ hdr).mpr
    exact_mod_cast hh
  constructor
  · calc
      _ ≤  ((p:ℝ)*a.lo/d)/S := div_le_div_of_nonneg_right hlr hSr.le
      _ = (p:ℝ)*((a.lo:ℝ)/S)/d := by ring
      _ ≤  _ := by gcongr; exact ha.1
  · calc
      _ ≤  (p:ℝ)*((a.hi:ℝ)/S)/d := by gcongr; exact ha.2
      _ = ((p:ℝ)*a.hi/d)/S := by ring
      _ ≤  _ := div_le_div_of_nonneg_right hhr hSr.le

/-- Linear integer inequalities certify a whole normalized power jet. The
proposed boxes may be generated by any method; their construction is not trusted. -/
theorem powerJet_enclosure {S d : ℕ} (hS : 0< S) (hd : 0< d) (p N : ℕ)
    (b : ℕ → Box) (x : ℝ) (h0 : Contains S (b 0) x)
    (hstep : ∀ j, j+1< N →
      (b (j+1)).lo*(d*(j+1))≤ p*(b j).lo ∧
      p*(b j).hi≤ (b (j+1)).hi*(d*(j+1))) :
    ∀ j< N, Contains S (b j) (x*((p:ℝ)/d)^j/(j.factorial:ℝ)) := by
  intro j
  induction j with
  | zero => intro hj; simpa using h0
  | succ j ih =>
    intro hj
    have hc := hstep j hj
    have hs := rationalStep_sound hS (Nat.mul_pos hd (Nat.succ_pos j)) p
      (ih (by omega)) hc.1 hc.2
    convert hs using 1
    push_cast
    rw [Nat.factorial_succ,pow_succ]
    push_cast
    field_simp

end CertifiedFixedPoint

end Height100Module49

/- Source module: SmallThetaJet. -/
section Height100Module50

open Complex Metric Real
namespace CertifiedZetaQuadrature

noncomputable def thetaTerm (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

end CertifiedZetaQuadrature

end Height100Module50

/- Source module: FullThetaTerms. -/
section Height100Module51

open Complex Metric Finset
namespace CertifiedZetaQuadrature
set_option exponentiation.threshold 512
open CertifiedTaylorQuadrature CertifiedMomentConvolution

noncomputable def fullThetaTerm (n : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

lemma fullThetaTerm_factor (n : ℕ) (z : ℂ) :
    fullThetaTerm n z=2*Complex.exp (z/4)*thetaTerm n z := by
  unfold fullThetaTerm thetaTerm
  rw [show z/4-(Real.pi:ℂ)*(n+1)^2*Complex.exp z =
    z/4+(-(Real.pi:ℂ)*(n+1)^2*Complex.exp z) by ring,Complex.exp_add]
  ring

lemma fullThetaTerm_entire (n : ℕ) : Differentiable ℂ (fullThetaTerm n) := by
  unfold fullThetaTerm
  fun_prop

noncomputable def baseKernel (z : ℂ) : ℂ := ∑ n ∈ range 8, fullThetaTerm n z

lemma baseKernel_entire : Differentiable ℂ baseKernel := by
  unfold baseKernel fullThetaTerm
  fun_prop

lemma baseKernel_eq (z : ℂ) : baseKernel z=2*Complex.exp (z/4)*thetaTruncation z := by
  unfold baseKernel
  simp_rw [fullThetaTerm_factor]
  rw [← mul_sum]
  rfl

lemma globalKernelMoment_base (k : ℕ) (z : ℂ) :
    globalKernelMoment k z=((64*z)^k/(k.factorial:ℂ))*baseKernel z := by
  rw [baseKernel_eq]
  unfold globalKernelMoment
  ring

end CertifiedZetaQuadrature

end Height100Module51

/- Source module: FullThetaODE. -/
section Height100Module52

open Complex Finset
namespace CertifiedZetaQuadrature
open CertifiedTaylorQuadrature CertifiedMomentConvolution CertifiedExponentialJets

noncomputable def thetaExponent (m : ℕ) (z : ℂ) : ℂ :=
  z/4-(Real.pi:ℂ)*(m+1)^2*Complex.exp z

lemma thetaExponent_entire (m : ℕ) : Differentiable ℂ (thetaExponent m) := by
  unfold thetaExponent
  fun_prop

lemma scaled_linear_quarter (c h : ℂ) (j : ℕ) :
    scaledCoefficient (fun z : ℂ => z/4) c h j =
      if j=0 then c/4 else if j=1 then h/4 else 0 := by
  unfold scaledCoefficient coefficient
  rw [iteratedDeriv_div_const,iteratedDeriv_fun_id]
  rcases j with _|j
  · simp
  rcases j with _|j
  · simp; ring
  · simp

lemma scaled_const_exp (a c h : ℂ) (j : ℕ) :
    scaledCoefficient (fun z => a*Complex.exp z) c h j =
      a*Complex.exp c*h^j/(j.factorial:ℂ) := by
  unfold scaledCoefficient coefficient
  rw [iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate,Complex.iter_deriv_exp]
  ring

lemma thetaExponent_scaled (m j : ℕ) (c h : ℝ) :
    scaledCoefficient (thetaExponent m) c h j =
      (if j=0 then (c:ℂ)/4 else if j=1 then (h:ℂ)/4 else 0) -
        ((Real.pi*(m+1:ℝ)^2*Real.exp c:ℝ):ℂ)*(h:ℂ)^j/(j.factorial:ℂ) := by
  have hlin : Differentiable ℂ (fun z : ℂ => z/4) := by fun_prop
  have hexp : Differentiable ℂ (fun z : ℂ => (Real.pi:ℂ)*(m+1)^2*Complex.exp z) := by fun_prop
  have hsplit : scaledCoefficient (thetaExponent m) c h j =
      scaledCoefficient (fun z : ℂ => z/4) c h j-
      scaledCoefficient (fun z : ℂ => (Real.pi:ℂ)*(m+1)^2*Complex.exp z) c h j := by
    unfold scaledCoefficient thetaExponent
    rw [CertifiedComplexTaylor.coefficient_sub _ _ hlin hexp]
    ring
  rw [hsplit,scaled_linear_quarter,scaled_const_exp]
  push_cast
  ring

lemma fullThetaTerm_scaled (m : ℕ) (c h : ℂ) (j : ℕ) :
    scaledCoefficient (fullThetaTerm m) c h j =
      2*scaledCoefficient (fun z => Complex.exp (thetaExponent m z)) c h j := by
  unfold scaledCoefficient coefficient fullThetaTerm thetaExponent
  rw [iteratedDeriv_const_mul_field]
  ring

lemma fullThetaTerm_ode (m : ℕ) (c h : ℂ) (n : ℕ) :
    (n+1:ℂ)*scaledCoefficient (fullThetaTerm m) c h (n+1)=
      ∑ k ∈ range (n+1), (k+1:ℂ)*scaledCoefficient (thetaExponent m) c h (k+1)*
        scaledCoefficient (fullThetaTerm m) c h (n-k) := by
  simp_rw [fullThetaTerm_scaled]
  have hr := scaled_exp_coefficient_recurrence (thetaExponent m) (thetaExponent_entire m) c h n
  have h2 := congrArg (fun z : ℂ => 2*z) hr
  rw [mul_sum] at h2
  convert! h2 using 1
  · ring
  · apply sum_congr rfl
    intro k _
    ring

end CertifiedZetaQuadrature

end Height100Module52


