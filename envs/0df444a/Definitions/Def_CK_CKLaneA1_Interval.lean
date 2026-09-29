-- Prove2me | Definitions.Def_CK_CKLaneA1_Interval
-- name    : CK_CKLaneA1_Interval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:01:06.272978+00:00
-- url     : https://prove2.me/theorems/89b7f6c7-d759-423a-a893-fef89dcd6191
-- title:
--   Courtade–Kumar proof module `CKLaneA1.Interval` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.Interval` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.Interval` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.Interval (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/Interval.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
import Definitions.Def_CK_CKLaneA1_Identities

/-!
# CKLaneA1.Interval — dyadic interval helpers, logs, series, and the two scaled formulas

All interval data are `GeneralCK.Certificates.DyadicInterval 64` (integer endpoints at scale
`2^64`), reusing the corpus soundness lemmas.  Everything executable is integer arithmetic
evaluated by the kernel (`decide +kernel`); no `native_decide`.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK.Certificates

abbrev DI := DyadicInterval 64

theorem SC_pos : (0:ℝ) < (DyadicInterval.scale 64 : ℝ) := DyadicInterval.scale_cast_pos 64

namespace Iv

def pt (a : ℤ) : DI := ⟨a, a⟩
def mk (lo hi : ℤ) : DI := ⟨lo, hi⟩
def one : DI := DyadicInterval.ofInt 64 1
def two : DI := DyadicInterval.ofInt 64 2
def zero : DI := DyadicInterval.ofInt 64 0

theorem pt_contains (a : ℤ) : (pt a).Contains ((a:ℝ)/(DyadicInterval.scale 64 : ℝ)) := by
  have hs := SC_pos
  have h : (DyadicInterval.scale 64 : ℝ) * ((a:ℝ)/(DyadicInterval.scale 64 : ℝ)) = a := by
    field_simp
  exact ⟨by simp only [pt]; rw [h], by simp only [pt]; rw [h]⟩

theorem one_contains : one.Contains (1:ℝ) := by
  unfold one; simpa using DyadicInterval.ofInt_sound 64 1

theorem two_contains : two.Contains (2:ℝ) := by
  unfold two; simpa using DyadicInterval.ofInt_sound 64 2

theorem zero_contains : zero.Contains (0:ℝ) := by
  unfold zero; simpa using DyadicInterval.ofInt_sound 64 0

theorem ofInt_contains (z : ℤ) : (DyadicInterval.ofInt 64 z).Contains (z:ℝ) :=
  DyadicInterval.ofInt_sound 64 z

theorem mk_contains {lo hi : ℤ} {x : ℝ} (h1 : (lo:ℝ) ≤ (DyadicInterval.scale 64 : ℝ) * x) (h2 : (DyadicInterval.scale 64 : ℝ) * x ≤ hi) :
    (mk lo hi).Contains x := ⟨h1, h2⟩

/-- Monotone hull: if `a ≤ x ≤ b`, `A ∋ a`, `B ∋ b`, then `[A.lo, B.hi] ∋ x`. -/
theorem hull_contains {A B : DI} {a b x : ℝ} (hA : A.Contains a) (hB : B.Contains b)
    (hax : a ≤ x) (hxb : x ≤ b) : (mk A.lo B.hi).Contains x := by
  have hs := SC_pos
  refine ⟨hA.1.trans ?_, le_trans ?_ hB.2⟩
  · change (DyadicInterval.scale 64 : ℝ) * a ≤ (DyadicInterval.scale 64 : ℝ) * x
    exact mul_le_mul_of_nonneg_left hax hs.le
  · change (DyadicInterval.scale 64 : ℝ) * x ≤ (DyadicInterval.scale 64 : ℝ) * b
    exact mul_le_mul_of_nonneg_left hxb hs.le

/-- Lower bound only from `A`, upper from `B`. -/
theorem lohi_contains {A B : DI} {a b x : ℝ} (hA : A.Contains a) (hB : B.Contains b)
    (hax : a ≤ x) (hxb : x ≤ b) : (mk A.lo B.hi).Contains x := hull_contains hA hB hax hxb

def meet (A B : DI) : DI := mk (max A.lo B.lo) (min A.hi B.hi)

theorem meet_contains {A B : DI} {x : ℝ} (hA : A.Contains x) (hB : B.Contains x) :
    (meet A B).Contains x := by
  refine ⟨?_, ?_⟩
  · change ((max A.lo B.lo : ℤ) : ℝ) ≤ _
    rw [Int.cast_max]; exact max_le hA.1 hB.1
  · change _ ≤ ((min A.hi B.hi : ℤ) : ℝ)
    rw [Int.cast_min]; exact le_min hA.2 hB.2

theorem contains_pos {A : DI} {x : ℝ} (hA : A.Contains x) (h : 0 < A.lo) : 0 < x :=
  DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using h) hA

theorem contains_le_of_hi {A : DI} {x : ℝ} (hA : A.Contains x) : (DyadicInterval.scale 64 : ℝ) * x ≤ A.hi := hA.2
theorem contains_ge_of_lo {A : DI} {x : ℝ} (hA : A.Contains x) : (A.lo:ℝ) ≤ (DyadicInterval.scale 64 : ℝ) * x := hA.1

end Iv

/-! ## Logarithms -/

def ln2Iv (n : ℕ) : DI := DyadicLogSeries.enclosure (DyadicFastLog.fraction 64 1 3) n

theorem ln2Iv_guard : DyadicLogSeries.guard (DyadicFastLog.fraction 64 1 3) = true := by
  decide +kernel

theorem ln2Iv_contains (n : ℕ) : (ln2Iv n).Contains (Real.log 2) := by
  have ht := DyadicLogSeries.enclosure_sound ln2Iv_guard
    (DyadicFastLog.fraction_sound 64 1 (by norm_num : (0:ℤ) < 3)) n
  have h2 : (1 + ((1:ℤ):ℝ) / ((3:ℤ):ℝ)) / (1 - ((1:ℤ):ℝ) / ((3:ℤ):ℝ)) = 2 := by norm_num
  rw [h2] at ht
  exact ht

/-- `log (a/b)` enclosure using a supplied `log 2` enclosure. -/
def logIv (L2 : DI) (a b : ℤ) (e n : ℕ) : DI :=
  (((DyadicInterval.ofInt 64 e).mul L2).add
    (DyadicLogSeries.enclosure (DyadicFastLog.reduced 64 a b e) n)).neg

def logOK (a b : ℤ) (e : ℕ) : Bool :=
  decide (0 < a ∧ 0 < b) && DyadicLogSeries.guard (DyadicFastLog.reduced 64 a b e)

theorem logIv_contains {L2 : DI} (hL : L2.Contains (Real.log 2)) {a b : ℤ} {e n : ℕ}
    (hc : logOK a b e = true) : (logIv L2 a b e n).Contains (Real.log ((a:ℝ)/b)) := by
  have h1 := Bool.and_eq_true_iff.mp hc
  have hab : 0 < a ∧ 0 < b := of_decide_eq_true h1.1
  have ha : (0:ℝ) < a := by exact_mod_cast hab.1
  have hb : (0:ℝ) < b := by exact_mod_cast hab.2
  have hd : 0 < b + a*2^e := add_pos hab.2 (mul_pos hab.1 (by positivity))
  have hr := DyadicLogSeries.enclosure_sound h1.2 (DyadicFastLog.fraction_sound 64 (b-a*2^e) hd) n
  have heq : (1+((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ))/
      (1-((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ)) = (b:ℝ)/(a*2^e) := by
    push_cast
    have hp : (0:ℝ)<2^e := by positivity
    field_simp
    ring
  rw [heq] at hr
  have hs := DyadicInterval.neg_sound (DyadicInterval.add_sound
    (DyadicInterval.mul_sound (DyadicInterval.ofInt_sound 64 e) hL) hr)
  have hl : -((e:ℝ)*Real.log 2+Real.log ((b:ℝ)/(a*2^e))) = Real.log ((a:ℝ)/b) := by
    rw [Real.log_div hb.ne' (mul_pos ha (by positivity)).ne',
      Real.log_mul ha.ne' (by positivity),Real.log_pow,Real.log_div ha.ne' hb.ne']
    ring
  simp only [Int.cast_natCast] at hs
  rw [hl] at hs
  exact hs

/-! ## Even power series for `log((1+x)/(1-x))/x` -/

/-- `(∑_{i<k} x^(2i)/(2i+1), x^(2k))` given an enclosure of `x^2`. -/
def serState (x2 : DI) : ℕ → DI × DI
  | 0 => (Iv.zero, Iv.one)
  | k+1 =>
      let t := serState x2 k
      (t.1.add (t.2.mul (DyadicInterval.ofInt 64 (2*(k:ℤ)+1)).recip), t.2.mul x2)

theorem serState_sound {x2 : DI} {x : ℝ} (hx : x2.Contains (x^2)) (k : ℕ) :
    (serState x2 k).1.Contains (∑ i ∈ Finset.range k, x^(2*i)/(2*i+1)) ∧
      (serState x2 k).2.Contains (x^(2*k)) := by
  induction k with
  | zero => simpa [serState] using And.intro Iv.zero_contains Iv.one_contains
  | succ k ih =>
    have hd : 0 < (DyadicInterval.ofInt 64 (2*(k:ℤ)+1)).lo := by
      change 0 < DyadicInterval.scale 64*(2*(k:ℤ)+1)
      exact mul_pos (DyadicInterval.scale_pos 64) (by omega)
    have hr := DyadicInterval.recip_sound hd (DyadicInterval.ofInt_sound 64 (2*(k:ℤ)+1))
    have ht := DyadicInterval.mul_sound ih.2 hr
    have hs := DyadicInterval.add_sound ih.1 ht
    have hp := DyadicInterval.mul_sound ih.2 hx
    constructor
    · simpa only [serState,Finset.sum_range_succ,Int.cast_add,Int.cast_mul,Int.cast_ofNat,
        Int.cast_one,Int.cast_natCast,div_eq_mul_inv] using hs
    · have he : (serState x2 (k+1)).2 = (serState x2 k).2.mul x2 := rfl
      have hx' : x^(2*(k+1)) = x^(2*k) * x^2 := by ring
      rw [he, hx']
      exact hp

/-! ## Interval versions of the two scaled formulas -/

def feTcoefIv (t qu ku Jw qw s S R W hh : DI) : DI :=
  let rs := s.recip
  let rS := S.recip
  let qj := ((qu.mul Jw).sub ku).mul rs
  let tj := ((t.mul Jw).sub Iv.one).mul rs
  let A1 := (qj.add ((Iv.two.mul qu).mul R)).sub Iv.one
  let U := (t.mul A1).add s
  let tJV := (((Iv.two.mul t).mul Jw).add ((A1.mul t).mul tj)).sub
    ((hh.sub s).mul (tj.add (Iv.two.mul (t.mul R))))
  let Z := (hh.sub s).sub ((ku.add (qw.mul Jw)).mul rS)
  let z := qu.neg.sub ((s.mul ku).mul rS)
  let m := ((qu.add qw).add (s.mul U)).sub (W.mul (z.mul z))
  let tJw := t.mul Jw
  let V1 := U.sub ((W.mul z).mul Z)
  (m.mul (tJV.sub ((tJw.mul W).mul (Z.mul Z)))).sub (tJw.mul (V1.mul V1))

theorem feTcoefIv_contains {t qu ku Jw qw s S R W hh : DI}
    {rt rqu rku rJw rqw rs rS rR rW rhh : ℝ}
    (ht : t.Contains rt) (hqu : qu.Contains rqu) (hku : ku.Contains rku)
    (hJw : Jw.Contains rJw) (hqw : qw.Contains rqw) (hs : s.Contains rs)
    (hS : S.Contains rS) (hR : R.Contains rR) (hW : W.Contains rW) (hhh : hh.Contains rhh)
    (hs0 : 0 < s.lo) (hS0 : 0 < S.lo) :
    (feTcoefIv t qu ku Jw qw s S R W hh).Contains (feTcoef rt rqu rku rJw rqw rs rS rR rW rhh) := by
  open DyadicInterval in
  have hrs := recip_sound hs0 hs
  have hrS := recip_sound hS0 hS
  have hqj := mul_sound (sub_sound (mul_sound hqu hJw) hku) hrs
  have htj := mul_sound (sub_sound (mul_sound ht hJw) Iv.one_contains) hrs
  have hA1 := sub_sound (add_sound hqj (mul_sound (mul_sound Iv.two_contains hqu) hR))
    Iv.one_contains
  have hU := add_sound (mul_sound ht hA1) hs
  have htJV := sub_sound (add_sound (mul_sound (mul_sound Iv.two_contains ht) hJw)
      (mul_sound (mul_sound hA1 ht) htj))
    (mul_sound (sub_sound hhh hs) (add_sound htj (mul_sound Iv.two_contains (mul_sound ht hR))))
  have hZ := sub_sound (sub_sound hhh hs) (mul_sound (add_sound hku (mul_sound hqw hJw)) hrS)
  have hz := sub_sound (neg_sound hqu) (mul_sound (mul_sound hs hku) hrS)
  have hm := sub_sound (add_sound (add_sound hqu hqw) (mul_sound hs hU))
    (mul_sound hW (mul_sound hz hz))
  have htJw := mul_sound ht hJw
  have hV1 := sub_sound hU (mul_sound (mul_sound hW hz) hZ)
  have hfin := sub_sound (mul_sound hm (sub_sound htJV (mul_sound (mul_sound htJw hW)
    (mul_sound hZ hZ)))) (mul_sound htJw (mul_sound hV1 hV1))
  simpa only [feTcoef, feTcoefIv, div_eq_mul_inv] using hfin

/-- As `feTcoefIv`, with the two divided-difference atoms `qj`, `tj` supplied. -/
def feTcoefIvJ (t qu ku Jw qw s S R W hh qj tj : DI) : DI :=
  let rS := S.recip
  let A1 := (qj.add ((Iv.two.mul qu).mul R)).sub Iv.one
  let U := (t.mul A1).add s
  let tJV := (((Iv.two.mul t).mul Jw).add ((A1.mul t).mul tj)).sub
    ((hh.sub s).mul (tj.add (Iv.two.mul (t.mul R))))
  let Z := (hh.sub s).sub ((ku.add (qw.mul Jw)).mul rS)
  let z := qu.neg.sub ((s.mul ku).mul rS)
  let m := ((qu.add qw).add (s.mul U)).sub (W.mul (z.mul z))
  let tJw := t.mul Jw
  let V1 := U.sub ((W.mul z).mul Z)
  (m.mul (tJV.sub ((tJw.mul W).mul (Z.mul Z)))).sub (tJw.mul (V1.mul V1))

theorem feTcoefIvJ_contains {t qu ku Jw qw s S R W hh qj tj : DI}
    {rt rqu rku rJw rqw rs rS rR rW rhh : ℝ}
    (ht : t.Contains rt) (hqu : qu.Contains rqu) (hku : ku.Contains rku)
    (hJw : Jw.Contains rJw) (hqw : qw.Contains rqw) (hs : s.Contains rs)
    (hS : S.Contains rS) (hR : R.Contains rR) (hW : W.Contains rW) (hhh : hh.Contains rhh)
    (hqj : qj.Contains ((rqu*rJw - rku)/rs)) (htj : tj.Contains ((rt*rJw - 1)/rs))
    (hS0 : 0 < S.lo) :
    (feTcoefIvJ t qu ku Jw qw s S R W hh qj tj).Contains
      (feTcoef rt rqu rku rJw rqw rs rS rR rW rhh) := by
  open DyadicInterval in
  have hrS := recip_sound hS0 hS
  have hA1 := sub_sound (add_sound hqj (mul_sound (mul_sound Iv.two_contains hqu) hR))
    Iv.one_contains
  have hU := add_sound (mul_sound ht hA1) hs
  have htJV := sub_sound (add_sound (mul_sound (mul_sound Iv.two_contains ht) hJw)
      (mul_sound (mul_sound hA1 ht) htj))
    (mul_sound (sub_sound hhh hs) (add_sound htj (mul_sound Iv.two_contains (mul_sound ht hR))))
  have hZ := sub_sound (sub_sound hhh hs) (mul_sound (add_sound hku (mul_sound hqw hJw)) hrS)
  have hz := sub_sound (neg_sound hqu) (mul_sound (mul_sound hs hku) hrS)
  have hm := sub_sound (add_sound (add_sound hqu hqw) (mul_sound hs hU))
    (mul_sound hW (mul_sound hz hz))
  have htJw := mul_sound ht hJw
  have hV1 := sub_sound hU (mul_sound (mul_sound hW hz) hZ)
  have hfin := sub_sound (mul_sound hm (sub_sound htJV (mul_sound (mul_sound htJw hW)
    (mul_sound hZ hZ)))) (mul_sound htJw (mul_sound hV1 hV1))
  simpa only [feTcoef, feTcoefIvJ, div_eq_mul_inv] using hfin

def feM11Iv (t qu ku Jw s S F W hh : DI) : DI :=
  let rS := S.recip
  let z := qu.neg.sub ((s.mul ku).mul rS)
  ((qu.mul (Iv.one.add (t.mul (Jw.add (Iv.two.mul F))))).add (s.mul (hh.sub t))).sub
    (W.mul (z.mul z))

theorem feM11Iv_contains {t qu ku Jw s S F W hh : DI}
    {rt rqu rku rJw rs rS rF rW rhh : ℝ}
    (ht : t.Contains rt) (hqu : qu.Contains rqu) (hku : ku.Contains rku)
    (hJw : Jw.Contains rJw) (hs : s.Contains rs) (hS : S.Contains rS)
    (hF : F.Contains rF) (hW : W.Contains rW) (hhh : hh.Contains rhh) (hS0 : 0 < S.lo) :
    (feM11Iv t qu ku Jw s S F W hh).Contains (feM11 rt rqu rku rJw rs rS rF rW rhh) := by
  open DyadicInterval in
  have hrS := recip_sound hS0 hS
  have hz := sub_sound (neg_sound hqu) (mul_sound (mul_sound hs hku) hrS)
  have hfin := sub_sound (add_sound (mul_sound hqu (add_sound Iv.one_contains
      (mul_sound ht (add_sound hJw (mul_sound Iv.two_contains hF))))) (mul_sound hs (sub_sound hhh ht)))
    (mul_sound hW (mul_sound hz hz))
  simpa only [feM11, feM11Iv, div_eq_mul_inv] using hfin

#print axioms ln2Iv_contains
#print axioms logIv_contains
#print axioms serState_sound
#print axioms feTcoefIv_contains
#print axioms feTcoefIvJ_contains
#print axioms Iv.meet_contains
#print axioms feM11Iv_contains

end CKLaneA1


