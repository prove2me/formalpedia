-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_StrictMonotoneInverse
-- name    : liuyao_ca_fd889115_k1_Analysis_StrictMonotoneInverse
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:56:33.215629+00:00
-- url     : https://prove2.me/theorems/860383fc-9dc5-4e73-8a3d-89553d46589d
-- title:
--   Computable analysis · StrictMonotoneInverse · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/StrictMonotoneInverse.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Numbers

set_option autoImplicit true

/-!
# Constructive inversion from strict increase

The primary function is sampled on rationals. Continuity means that a supplied
interval extension sends every valid input name to a valid output name. Its
coverage law connects that extension to the primary samples; no uniform
continuity modulus or inverse-separation schedule is requested.

Two interior rational points avoid deciding equality with the target. Strict
increase proves that a decidable separation search terminates. The resulting
nested intervals construct the preimage, including for irrational targets.
-/
namespace ComputableAnalysis.StrictMonotoneInverse

def Source (F : FunctionOnInterval) (x : RealCompute) : Prop :=
  ∀ n, subintervalOf (x.compute n) F.lower F.upper

def sample (F : FunctionOnInterval) (q : Rat)
    (hq : inDomainInterval F.lower F.upper q) : RealCompute where
  compute := F.compute q hq

theorem sample_valid (F : FunctionOnInterval) (q : Rat)
    (hq : inDomainInterval F.lower F.upper q) : (sample F q hq).Valid :=
  F.valid_on q (F.defined_on q hq)

/-- Strict order of the rational samples, as an exact represented inequality.
The witness is only a proof of eventual separation, not a supplied schedule. -/
def StrictlyIncreasing (F : FunctionOnInterval) : Prop :=
  ∀ (p q : Rat) (hp : inDomainInterval F.lower F.upper p)
    (hq : inDomainInterval F.lower F.upper q), p < q →
    ∃ n, (F.compute p hp n).hi < (F.compute q hq n).lo

/-- An interval extension with justified rational coverage. The stage is
implementation data explaining which input enclosure an output encloses. -/
structure Extension (F : FunctionOnInterval) where
  eval : (x : RealCompute) → x.Valid → Source F x → RealCompute
  stage : (x : RealCompute) → x.Valid → Source F x → Nat → Nat
  encloses : ∀ x hx hs n q hq,
    (x.compute (stage x hx hs n)).lo ≤ q →
    q ≤ (x.compute (stage x hx hs n)).hi →
    ((eval x hx hs).compute n).ContainsInterval (F.compute q hq n)

/-- The validity-based continuity requirement, without a chosen modulus. -/
def Extension.Continuous {F : FunctionOnInterval} (E : Extension F) : Prop :=
  ∀ x hx hs, (E.eval x hx hs).Valid

/-- Membership of the source interval is a value-level condition; early name
intervals need not already lie in the source interval. -/
def InSource (F : FunctionOnInterval) (x : RealCompute) : Prop :=
  (RealCompute.ofRat F.lower).Le x ∧ x.Le (RealCompute.ofRat F.upper)

private def ratMax (a b : Rat) : Rat := if a ≤ b then b else a
private def ratMin (a b : Rat) : Rat := if a ≤ b then a else b

/-- Repair a supplied name to the closed source interval, including endpoints. -/
def clip (F : FunctionOnInterval) (x : RealCompute) : RealCompute where
  compute n := ⟨ratMax F.lower (x.compute n).lo,ratMin F.upper (x.compute n).hi⟩

theorem clip_source {F : FunctionOnInterval} (hab : F.lower ≤ F.upper)
    (x : RealCompute) (hx : x.Valid) (hs : InSource F x) : Source F (clip F x) := by
  intro n
  have hlo := hs.1 0 n
  have hhi := hs.2 n 0
  have ho := RealCompute.interval_order_of_valid x hx n
  change F.lower ≤ (x.compute n).hi at hlo
  change (x.compute n).lo ≤ F.upper at hhi
  dsimp [clip,subintervalOf,ratMax,ratMin]
  split <;> split <;> grind

theorem clip_valid {F : FunctionOnInterval} (hab : F.lower ≤ F.upper)
    (x : RealCompute) (hx : x.Valid) (hs : InSource F x) : (clip F x).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have ho := (clip_source hab x hx hs n).2.1
    dsimp [QInterval.width]; grind
  · intro n m hnm
    have hm := clip_source hab x hx hs m
    have hnest := hx.2.1 n m hnm
    refine ⟨?_,hm.2.1,?_⟩
    · dsimp [clip,ratMax]
      split <;> split <;> grind
    · dsimp [clip,ratMin]
      split <;> split <;> grind
  · intro eps
    obtain ⟨N,hN⟩ := hx.2.2 eps
    refine ⟨N,?_⟩
    intro n hn
    have hw := hN n hn
    dsimp [clip,QInterval.width,ratMax,ratMin]
    split <;> split <;> dsimp [QInterval.width] at hw <;> grind

theorem clip_equiv {F : FunctionOnInterval} (_hab : F.lower ≤ F.upper)
    (x : RealCompute) (hx : x.Valid) (hs : InSource F x) : (clip F x).Equiv x := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).mpr
  have hlo := hs.1 0 n
  have hhi := hs.2 n 0
  have ho := RealCompute.interval_order_of_valid x hx n
  change F.lower ≤ (x.compute n).hi at hlo
  change (x.compute n).lo ≤ F.upper at hhi
  dsimp [clip,QInterval.Overlaps,ratMax,ratMin]
  split <;> split <;> grind

/-- Evaluation on the full mathematical source interval. Clipping is internal. -/
def Extension.evalOn {F : FunctionOnInterval} (E : Extension F)
    (hab : F.lower ≤ F.upper) (x : RealCompute) (hx : x.Valid) (hs : InSource F x) : RealCompute :=
  E.eval (clip F x) (clip_valid hab x hx hs) (clip_source hab x hx hs)

theorem sample_mono {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    {p q : Rat} (hp : inDomainInterval F.lower F.upper p)
    (hq : inDomainInterval F.lower F.upper q) (hpq : p ≤ q) :
    (sample F p hp).Le (sample F q hq) := by
  by_cases heq : p = q
  · subst q
    exact RealCompute.le_refl (sample F p hp) (sample_valid F p hp)
  · have hlt : p < q := by grind
    obtain ⟨k, hk⟩ := hstrict p q hp hq hlt
    intro n m
    have ha := RealCompute.le_refl (sample F p hp) (sample_valid F p hp) n k
    have hb := RealCompute.le_refl (sample F q hq) (sample_valid F q hq) k m
    change (F.compute p hp n).lo ≤ (F.compute q hq m).hi
    change (F.compute p hp n).lo ≤ (F.compute p hp k).hi at ha
    change (F.compute q hq k).lo ≤ (F.compute q hq m).hi at hb
    grind

private def next (p : Nat → Prop) (m n : Nat) : Prop := m = n+1 ∧ ¬ p n

private theorem accessible (p : Nat → Prop) (d n : Nat)
    (h : p (n+d)) : Acc (next p) n := by
  induction d generalizing n with
  | zero =>
    apply Acc.intro
    intro m hm
    exact False.elim (hm.2 (by simpa using h))
  | succ d ih =>
    apply Acc.intro
    intro m hm
    rcases hm with ⟨rfl, _⟩
    apply ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private def searchFrom (p : Nat → Prop) [DecidablePred p]
    (n : Nat) (h : Acc (next p) n) : {k // p k} :=
  Acc.rec (motive := fun _ _ => {k // p k})
    (fun n _ recurse => if hn : p n then ⟨n,hn⟩ else recurse (n+1) ⟨rfl,hn⟩) h

private theorem searchAccessible (p : Nat → Prop) (h : ∃ n, p n) : Acc (next p) 0 := by
  rcases h with ⟨n,hn⟩
  exact accessible p n 0 (by simpa using hn)

/-- Executable search: the existential proof justifies termination and is
erased. No arbitrary witness is extracted from that proof. -/
private def search (p : Nat → Prop) [DecidablePred p]
    (h : ∃ n,p n) : {n // p n} := searchFrom p 0 (searchAccessible p h)

structure Bracket (F : FunctionOnInterval) (y : RealCompute) where
  interval : QInterval
  inside : subintervalOf interval F.lower F.upper
  lower_le : (sample F interval.lo ⟨inside.1, by grind [inside.2.1, inside.2.2]⟩).Le y
  le_upper : y.Le (sample F interval.hi ⟨by grind [inside.1, inside.2.1], inside.2.2⟩)

private def leftThird (I : QInterval) : Rat := (2*I.lo+I.hi)/3
private def rightThird (I : QInterval) : Rat := (I.lo+2*I.hi)/3

private theorem thirds {I : QInterval} (h : I.lo < I.hi) :
    I.lo ≤ leftThird I ∧ leftThird I < rightThird I ∧ rightThird I ≤ I.hi := by
  dsimp [leftThird,rightThird]
  grind

private theorem separated_decision {F : FunctionOnInterval}
    (hstrict : StrictlyIncreasing F) (y : RealCompute) (hy : y.Valid)
    (l r : Rat) (hl : inDomainInterval F.lower F.upper l)
    (hr : inDomainInterval F.lower F.upper r) (hlr : l < r) :
    ∃ k, (F.compute l hl k).hi < (y.compute k).lo ∨
      (y.compute k).hi < (F.compute r hr k).lo := by
  obtain ⟨j,hj⟩ := hstrict l r hl hr hlr
  let eps : QPos := ⟨((F.compute r hr j).lo-(F.compute l hl j).hi)/2, by grind⟩
  obtain ⟨N,hN⟩ := hy.2.2 eps
  let k := max N j
  have hw := hN k (Nat.le_max_left _ _)
  have hleft := (sample_valid F l hl).2.1 j k (Nat.le_max_right _ _)
  have hright := (sample_valid F r hr).2.1 j k (Nat.le_max_right _ _)
  refine ⟨k, ?_⟩
  dsimp [sample] at hleft hright
  dsimp [eps, QInterval.width] at hw
  grind

private theorem strict_separation_le {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    {k : Nat} (h : (x.compute k).hi < (y.compute k).lo) : x.Le y := by
  intro n m
  have ha := RealCompute.le_refl x hx n k
  have hb := RealCompute.le_refl y hy k m
  grind

def step {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (y : RealCompute) (hy : y.Valid) (B : Bracket F y) : Bracket F y := by
  by_cases hpos : B.interval.lo < B.interval.hi
  · let l := leftThird B.interval
    let r := rightThird B.interval
    have ht := thirds hpos
    have hb := B.inside
    dsimp [subintervalOf] at hb
    have hl : inDomainInterval F.lower F.upper l := by
      dsimp [inDomainInterval]
      exact ⟨by grind, by grind⟩
    have hr : inDomainInterval F.lower F.upper r := by
      dsimp [inDomainInterval]
      exact ⟨by grind, by grind⟩
    let k := search (fun k => (F.compute l hl k).hi < (y.compute k).lo ∨
      (y.compute k).hi < (F.compute r hr k).lo)
      (separated_decision hstrict y hy l r hl hr ht.2.1)
    if hleft : (F.compute l hl k.val).hi < (y.compute k.val).lo then
      exact {
        interval := ⟨l,B.interval.hi⟩
        inside := ⟨hl.1, by grind, B.inside.2.2⟩
        lower_le := strict_separation_le (sample_valid F l hl) hy hleft
        le_upper := B.le_upper }
    else
      exact {
        interval := ⟨B.interval.lo,r⟩
        inside := ⟨B.inside.1, by grind, hr.2⟩
        lower_le := B.lower_le
        le_upper := strict_separation_le hy (sample_valid F r hr)
          (k.property.resolve_left hleft) }
  · exact B

theorem step_bounds {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (y : RealCompute) (hy : y.Valid) (B : Bracket F y) :
    B.interval.lo ≤ (step hstrict y hy B).interval.lo ∧
    (step hstrict y hy B).interval.hi ≤ B.interval.hi ∧
    3*(step hstrict y hy B).interval.width ≤ 2*B.interval.width := by
  unfold step
  split
  · dsimp only
    split
    · dsimp [leftThird,QInterval.width]
      grind
    · dsimp [rightThird,QInterval.width]
      grind
  · have ho := B.inside.2.1
    dsimp [QInterval.width]
    grind

def initial {F : FunctionOnInterval} (hab : F.lower ≤ F.upper)
    (y : RealCompute)
    (ha : (sample F F.lower ⟨Rat.le_refl,hab⟩).Le y)
    (hb : y.Le (sample F F.upper ⟨hab,Rat.le_refl⟩)) : Bracket F y where
  interval := ⟨F.lower,F.upper⟩
  inside := ⟨Rat.le_refl,hab,Rat.le_refl⟩
  lower_le := ha
  le_upper := hb

def iterate {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (y : RealCompute) (hy : y.Valid) (B : Bracket F y) : Nat → Bracket F y
  | 0 => B
  | n+1 => step hstrict y hy (iterate hstrict y hy B n)

theorem iterate_nested {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (y : RealCompute) (hy : y.Valid) (B : Bracket F y) (n m : Nat) (hnm : n ≤ m) :
    (iterate hstrict y hy B n).interval.lo ≤ (iterate hstrict y hy B m).interval.lo ∧
    (iterate hstrict y hy B m).interval.hi ≤ (iterate hstrict y hy B n).interval.hi := by
  induction m with
  | zero =>
    have : n=0 := by omega
    subst n
    exact ⟨Rat.le_refl,Rat.le_refl⟩
  | succ m ih =>
    by_cases h : n ≤ m
    · have hi := ih h
      have hs := step_bounds hstrict y hy (iterate hstrict y hy B m)
      exact ⟨Rat.le_trans hi.1 hs.1,Rat.le_trans hs.2.1 hi.2⟩
    · have : n=m+1 := by omega
      subst n
      exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem iterate_weighted_width {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (y : RealCompute) (hy : y.Valid) (B : Bracket F y) (n : Nat) :
    ((n:Rat)+2)*(iterate hstrict y hy B n).interval.width ≤ 2*B.interval.width := by
  induction n with
  | zero => change ((0:Rat)+2)*B.interval.width ≤ 2*B.interval.width; grind
  | succ n ih =>
    have hs := (step_bounds hstrict y hy (iterate hstrict y hy B n)).2.2
    have ho := (iterate hstrict y hy B n).inside.2.1
    have hw : 0 ≤ (iterate hstrict y hy B n).interval.width := by
      dsimp [QInterval.width]; grind
    have hn : (0:Rat) ≤ n := Rat.natCast_nonneg
    have hm := Rat.mul_le_mul_of_nonneg_left hs (by grind : (0:Rat) ≤ (n:Rat)+3)
    have hp := Rat.mul_nonneg hn hw
    simp only [Rat.natCast_add]
    change (((n:Rat)+1)+2)*(step hstrict y hy (iterate hstrict y hy B n)).interval.width ≤ _
    grind

private theorem div_bound {u v d : Rat} (hd : 0 < d) (h : d*u ≤ v) : u ≤ v/d := by
  have hc := Rat.inv_mul_cancel d (by grind : d≠0)
  have hm := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt (Rat.inv_pos.mpr hd))
  calc
    u = d⁻¹*(d*u) := by rw [← Rat.mul_assoc, hc, Rat.one_mul]
    _ ≤ d⁻¹*v := hm
    _ = v/d := by rw [Rat.div_def, Rat.mul_comm]

theorem iterate_valid {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (y : RealCompute) (hy : y.Valid) (B : Bracket F y) :
    RealCompute.ValidCompute (fun n => (iterate hstrict y hy B n).interval) := by
  refine ⟨?_,?_,?_⟩
  · intro n
    have ho := (iterate hstrict y hy B n).inside.2.1
    dsimp [QInterval.width]; grind
  · intro n m hnm
    have hn := iterate_nested hstrict y hy B n m hnm
    exact ⟨hn.1,(iterate hstrict y hy B m).inside.2.1,hn.2⟩
  · apply shrinksToZero_of_ratOverSuccBound (C := 2*B.interval.width)
    intro n
    have hw := iterate_weighted_width hstrict y hy B n
    have ho := (iterate hstrict y hy B n).inside.2.1
    have hn : (0:Rat) < ((n+1:Nat):Rat) := Rat.natCast_pos.mpr (by omega)
    apply div_bound hn
    simp only [Rat.natCast_add]
    dsimp [QInterval.width] at *
    grind

/-- Interval coverage and rational order imply order of the derived evaluations,
even for different implementations of the extension. -/
theorem Extension.eval_mono {F : FunctionOnInterval} (E G : Extension F)
    (hstrict : StrictlyIncreasing F) (x z : RealCompute) (hx : x.Valid) (hz : z.Valid)
    (hsx : Source F x) (hsz : Source F z) (h : x.Le z) :
    (E.eval x hx hsx).Le (G.eval z hz hsz) := by
  intro n m
  let i := E.stage x hx hsx n
  let j := G.stage z hz hsz m
  let a := (x.compute i).lo
  let b := (z.compute j).hi
  have hxi := hsx i
  have hzj := hsz j
  have ha : inDomainInterval F.lower F.upper a :=
    ⟨hxi.1,Rat.le_trans hxi.2.1 hxi.2.2⟩
  have hb : inDomainInterval F.lower F.upper b :=
    ⟨Rat.le_trans hzj.1 hzj.2.1,hzj.2.2⟩
  have he := E.encloses x hx hsx n a ha Rat.le_refl hxi.2.1
  have hg := G.encloses z hz hsz m b hb hzj.2.1 Rat.le_refl
  have hm := sample_mono hstrict ha hb (h i j) n m
  exact Rat.le_trans he.1 (Rat.le_trans hm hg.2)

/-- Equivalent names, and alternate covered extensions, give the same value. -/
theorem Extension.eval_equiv {F : FunctionOnInterval} (E G : Extension F)
    (hstrict : StrictlyIncreasing F) (x z : RealCompute) (hx : x.Valid) (hz : z.Valid)
    (hsx : Source F x) (hsz : Source F z) (h : x.Equiv z) :
    (E.eval x hx hsx).Equiv (G.eval z hz hsz) := by
  apply RealCompute.le_antisymm
  · exact E.eval_mono G hstrict x z hx hz hsx hsz (RealCompute.le_of_equiv hx hz h)
  · exact G.eval_mono E hstrict z x hz hx hsz hsx
      (RealCompute.le_of_equiv hz hx (RealCompute.equiv_symm h))

private theorem Extension.eval_le_sample {F : FunctionOnInterval} (E : Extension F)
    (hstrict : StrictlyIncreasing F) (x : RealCompute) (hx : x.Valid) (hs : Source F x)
    (q : Rat) (hq : inDomainInterval F.lower F.upper q)
    (hbound : ∀ k, (x.compute k).lo ≤ q) :
    (E.eval x hx hs).Le (sample F q hq) := by
  intro n m
  let i := E.stage x hx hs n
  have hi := hs i
  have ha : inDomainInterval F.lower F.upper (x.compute i).lo :=
    ⟨hi.1,Rat.le_trans hi.2.1 hi.2.2⟩
  have he := E.encloses x hx hs n _ ha Rat.le_refl hi.2.1
  exact Rat.le_trans he.1 (sample_mono hstrict ha hq (hbound i) n m)

private theorem Extension.sample_le_eval {F : FunctionOnInterval} (E : Extension F)
    (hstrict : StrictlyIncreasing F) (x : RealCompute) (hx : x.Valid) (hs : Source F x)
    (q : Rat) (hq : inDomainInterval F.lower F.upper q)
    (hbound : ∀ k, q ≤ (x.compute k).hi) :
    (sample F q hq).Le (E.eval x hx hs) := by
  intro n m
  let i := E.stage x hx hs m
  have hi := hs i
  have hb : inDomainInterval F.lower F.upper (x.compute i).hi :=
    ⟨Rat.le_trans hi.1 hi.2.1,hi.2.2⟩
  have he := E.encloses x hx hs m _ hb hi.2.1 Rat.le_refl
  exact Rat.le_trans (sample_mono hstrict hq hb (hbound i) n m) he.2

/-- Strict increase survives passage from rational samples to valid inputs.
Equality of evaluated values therefore determines a unique source value. -/
theorem Extension.injective {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (x z : RealCompute) (hx : x.Valid) (hz : z.Valid)
    (hsx : Source F x) (hsz : Source F z)
    (heq : (E.eval x hx hsx).Equiv (E.eval z hz hsz)) : x.Equiv z := by
  have direction : ∀ (u v : RealCompute) (hu : u.Valid) (hv : v.Valid)
      (hsu : Source F u) (hsv : Source F v),
      (E.eval u hu hsu).Le (E.eval v hv hsv) → u.Le v := by
    intro u v hu hv hsu hsv huv n m
    by_cases hnot : (u.compute n).lo ≤ (v.compute m).hi
    · exact hnot
    exfalso
    have hlt : (v.compute m).hi < (u.compute n).lo := by grind
    have hn := hsu n
    have hm := hsv m
    have hp : inDomainInterval F.lower F.upper (v.compute m).hi :=
      ⟨Rat.le_trans hm.1 hm.2.1,hm.2.2⟩
    have hq : inDomainInterval F.lower F.upper (u.compute n).lo :=
      ⟨hn.1,Rat.le_trans hn.2.1 hn.2.2⟩
    have hqle := E.sample_le_eval hstrict u hu hsu _ hq
      (fun k => RealCompute.le_refl u hu n k)
    have hple := E.eval_le_sample hstrict v hv hsv _ hp
      (fun k => RealCompute.le_refl v hv k m)
    have hreverse := RealCompute.le_trans (hcontinuous v hv hsv)
      (RealCompute.le_trans (hcontinuous u hu hsu) hqle huv) hple
    obtain ⟨k,hk⟩ := hstrict _ _ hp hq hlt
    have hcontra := hreverse k k
    change (F.compute _ hq k).lo ≤ (F.compute _ hp k).hi at hcontra
    grind
  exact RealCompute.le_antisymm
    (direction x z hx hz hsx hsz
      (RealCompute.le_of_equiv (hcontinuous x hx hsx) (hcontinuous z hz hsz) heq))
    (direction z x hz hx hsz hsx
      (RealCompute.le_of_equiv (hcontinuous z hz hsz) (hcontinuous x hx hsx)
        (RealCompute.equiv_symm heq)))

def InRange (F : FunctionOnInterval) (hab : F.lower ≤ F.upper) (y : RealCompute) : Prop :=
  (sample F F.lower ⟨Rat.le_refl,hab⟩).Le y ∧
    y.Le (sample F F.upper ⟨hab,Rat.le_refl⟩)

/-- The preimage algorithm. It needs strict rational order and endpoint range;
continuity is used separately to identify its forward value. -/
def inverse {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : RealCompute) (hy : y.Valid) (hr : InRange F hab y) :
    RealCompute where
  compute := fun n => (iterate hstrict y hy (initial hab y hr.1 hr.2) n).interval

theorem inverse_valid {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : RealCompute) (hy : y.Valid) (hr : InRange F hab y) :
    (inverse hstrict hab y hy hr).Valid :=
  iterate_valid hstrict y hy (initial hab y hr.1 hr.2)

theorem inverse_source {F : FunctionOnInterval} (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : RealCompute) (hy : y.Valid) (hr : InRange F hab y) :
    Source F (inverse hstrict hab y hy hr) :=
  fun n => (iterate hstrict y hy (initial hab y hr.1 hr.2) n).inside

/-- Exact constructive intermediate value theorem, for every valid represented
target in the endpoint range. The constructed name is the witness. -/
theorem inverse_target {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : RealCompute) (hy : y.Valid) (hr : InRange F hab y) :
    (E.eval (inverse hstrict hab y hy hr)
      (inverse_valid hstrict hab y hy hr)
      (inverse_source hstrict hab y hy hr)).Equiv y := by
  let x := inverse hstrict hab y hy hr
  let hx := inverse_valid hstrict hab y hy hr
  let hs := inverse_source hstrict hab y hy hr
  have hov : ∀ n, ((E.eval x hx hs).compute n).Overlaps (y.compute n) := by
    intro n
    let k := E.stage x hx hs n
    let B := iterate hstrict y hy (initial hab y hr.1 hr.2) k
    have hlo := E.encloses x hx hs n B.interval.lo
      ⟨B.inside.1,Rat.le_trans B.inside.2.1 B.inside.2.2⟩ Rat.le_refl B.inside.2.1
    have hhi := E.encloses x hx hs n B.interval.hi
      ⟨Rat.le_trans B.inside.1 B.inside.2.1,B.inside.2.2⟩ B.inside.2.1 Rat.le_refl
    exact ⟨Rat.le_trans hlo.1 (B.lower_le n n),Rat.le_trans (B.le_upper n n) hhi.2⟩
  exact RealCompute.le_antisymm
    (RealCompute.le_of_sameStage (hcontinuous x hx hs) hy (fun n => (hov n).1))
    (RealCompute.le_of_sameStage hy (hcontinuous x hx hs) (fun n => (hov n).2))

/-- Every supplied valid solution in the interval equals the constructed one. -/
theorem inverse_unique {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : RealCompute) (hy : y.Valid) (hr : InRange F hab y)
    (z : RealCompute) (hz : z.Valid) (hsz : Source F z)
    (hsolution : (E.eval z hz hsz).Equiv y) :
    (inverse hstrict hab y hy hr).Equiv z := by
  apply E.injective hcontinuous hstrict _ z (inverse_valid hstrict hab y hy hr) hz
    (inverse_source hstrict hab y hy hr) hsz
  exact RealCompute.equiv_trans
    (hcontinuous _ (inverse_valid hstrict hab y hy hr) (inverse_source hstrict hab y hy hr))
    hy (hcontinuous z hz hsz)
    (inverse_target E hcontinuous hstrict hab y hy hr) (RealCompute.equiv_symm hsolution)

/-- Equivalent target names produce equivalent inverse names. -/
theorem inverse_congr {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y z : RealCompute) (hy : y.Valid) (hz : z.Valid)
    (hry : InRange F hab y) (hrz : InRange F hab z) (heq : y.Equiv z) :
    (inverse hstrict hab y hy hry).Equiv (inverse hstrict hab z hz hrz) := by
  apply inverse_unique E hcontinuous hstrict hab y hy hry _
    (inverse_valid hstrict hab z hz hrz) (inverse_source hstrict hab z hz hrz)
  exact RealCompute.equiv_trans
    (hcontinuous _ (inverse_valid hstrict hab z hz hrz) (inverse_source hstrict hab z hz hrz))
    hz hy (inverse_target E hcontinuous hstrict hab z hz hrz) (RealCompute.equiv_symm heq)

theorem Extension.eval_inRange {F : FunctionOnInterval} (E : Extension F)
    (hstrict : StrictlyIncreasing F) (hab : F.lower ≤ F.upper)
    (x : RealCompute) (hx : x.Valid) (hs : Source F x) :
    InRange F hab (E.eval x hx hs) := by
  constructor
  · exact E.sample_le_eval hstrict x hx hs _ ⟨Rat.le_refl,hab⟩
      (fun k => Rat.le_trans (hs k).1 (hs k).2.1)
  · exact E.eval_le_sample hstrict x hx hs _ ⟨hab,Rat.le_refl⟩
      (fun k => Rat.le_trans (hs k).2.1 (hs k).2.2)

/-- The other inverse law holds for every valid source name in the interval. -/
theorem inverse_eval {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (x : RealCompute) (hx : x.Valid) (hs : Source F x) :
    (inverse hstrict hab (E.eval x hx hs) (hcontinuous x hx hs)
      (E.eval_inRange hstrict hab x hx hs)).Equiv x :=
  inverse_unique E hcontinuous hstrict hab _ (hcontinuous x hx hs)
    (E.eval_inRange hstrict hab x hx hs) x hx hs
    (RealCompute.equiv_refl _ (hcontinuous x hx hs))

/-- The inverse law on every valid name of a source value. Callers supply only
value membership, not a pre-clipped name or an internal precision schedule. -/
theorem inverse_evalOn {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (x : RealCompute) (hx : x.Valid) (hs : InSource F x) :
    (inverse hstrict hab (E.evalOn hab x hx hs)
      (hcontinuous _ (clip_valid hab x hx hs) (clip_source hab x hx hs))
      (E.eval_inRange hstrict hab _ (clip_valid hab x hx hs) (clip_source hab x hx hs))).Equiv x :=
  RealCompute.equiv_trans
    (inverse_valid hstrict hab _
      (hcontinuous _ (clip_valid hab x hx hs) (clip_source hab x hx hs))
      (E.eval_inRange hstrict hab _ (clip_valid hab x hx hs) (clip_source hab x hx hs)))
    (clip_valid hab x hx hs) hx
    (inverse_eval E hcontinuous hstrict hab _ (clip_valid hab x hx hs) (clip_source hab x hx hs))
    (clip_equiv hab x hx hs)

/-- The endpoint range as a predicate on mathematical real values. -/
def ValueInRange (F : FunctionOnInterval) (hab : F.lower ≤ F.upper)
    (y : ComputableAnalysis.Real) : Prop :=
  RealComputeQuotient.ofRaw (sample F F.lower ⟨Rat.le_refl,hab⟩)
    (sample_valid F F.lower ⟨Rat.le_refl,hab⟩) ≤ y ∧
  y ≤ RealComputeQuotient.ofRaw (sample F F.upper ⟨hab,Rat.le_refl⟩)
    (sample_valid F F.upper ⟨hab,Rat.le_refl⟩)

/-- The inverse on quotient values is executable by quotient lifting. Its
computation uses the supplied target name, with no representative choice. -/
def inverseValue {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : ComputableAnalysis.Real) (hr : ValueInRange F hab y) :
    ComputableAnalysis.Real := by
  refine Quotient.pliftOn y (fun c hc => ?_) ?_
  · have hr' : InRange F hab c.val := by
      change ValueInRange F hab (RealComputeQuotient.ofRaw c.val c.property)
      have hc' : y = RealComputeQuotient.ofRaw c.val c.property := hc
      rw [← hc']
      exact hr
    exact RealComputeQuotient.ofRaw (inverse hstrict hab c.val c.property hr')
      (inverse_valid hstrict hab c.val c.property hr')
  · intro a b ha hb hequiv
    apply RealComputeQuotient.ofRaw_eq_ofRaw
    exact inverse_congr E hcontinuous hstrict hab a.val b.val a.property b.property _ _ hequiv

@[simp] theorem inverseValue_ofRaw {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : RealCompute) (hy : y.Valid) (hr : InRange F hab y) :
    inverseValue E hcontinuous hstrict hab (RealComputeQuotient.ofRaw y hy) hr =
      RealComputeQuotient.ofRaw (inverse hstrict hab y hy hr)
        (inverse_valid hstrict hab y hy hr) := rfl

/-- The exact target law also holds as equality of mathematical real values. -/
theorem inverse_value_target {F : FunctionOnInterval} (E : Extension F)
    (hcontinuous : E.Continuous) (hstrict : StrictlyIncreasing F)
    (hab : F.lower ≤ F.upper) (y : RealCompute) (hy : y.Valid) (hr : InRange F hab y) :
    RealComputeQuotient.ofRaw
      (E.eval (inverse hstrict hab y hy hr) (inverse_valid hstrict hab y hy hr)
        (inverse_source hstrict hab y hy hr))
      (hcontinuous _ (inverse_valid hstrict hab y hy hr) (inverse_source hstrict hab y hy hr)) =
      RealComputeQuotient.ofRaw y hy :=
  RealComputeQuotient.ofRaw_eq_ofRaw (inverse_target E hcontinuous hstrict hab y hy hr)

end ComputableAnalysis.StrictMonotoneInverse


