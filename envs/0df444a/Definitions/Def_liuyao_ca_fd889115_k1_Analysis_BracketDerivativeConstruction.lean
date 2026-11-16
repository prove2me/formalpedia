-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BracketDerivativeConstruction
-- name    : liuyao_ca_fd889115_k1_Analysis_BracketDerivativeConstruction
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:55:19.557054+00:00
-- url     : https://prove2.me/theorems/d91c2b23-0528-460f-9111-5fd5b537e697
-- title:
--   Computable analysis · BracketDerivativeConstruction · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/BracketDerivativeConstruction.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BracketDerivative
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-! Executable admissible names, and the semantic bridge from literal outer
secant enclosures to derivatives at arbitrary valid represented inputs. -/
namespace ComputableAnalysis.BracketDerivative
set_option maxHeartbeats 2000000

/-! Compatibility names for the shared executable padded enclosure. -/
def allowance (n : Nat) : Rat := ((1:Rat)/2)^n
theorem allowance_pos (n : Nat) : 0 < allowance n := RawLimit.allowance_pos n
theorem allowance_antitone {n m : Nat} (h : n ≤ m) : allowance m ≤ allowance n :=
  RawLimit.allowance_antitone h
theorem allowance_shrinks (eps : QPos) : ∃ N, ∀ n, N ≤ n → allowance n ≤ eps.val :=
  RawLimit.allowance_shrinks eps
def enlarged (x : RealCompute) : RealCompute where
  compute n := QInterval.expand (x.compute n) (allowance n)
theorem enlarged_valid {x : RealCompute} (hx : x.Valid) : (enlarged x).Valid :=
  RawLimit.enlarged_valid hx
theorem enlarged_equiv {x : RealCompute} (hx : x.Valid) : (enlarged x).Equiv x :=
  RawLimit.enlarged_equiv hx

theorem enlarged_admissible {x : RealCompute} (hx : x.Valid) :
    Admissible (fun _ => True) x (enlarged x) := by
  refine ⟨hx,enlarged_valid hx,enlarged_equiv hx,fun n => ⟨?_,fun _ _ _ => True.intro⟩⟩
  have ho := hx.1 n
  have hp := allowance_pos n
  change (x.compute n).lo-allowance n<(x.compute n).hi+allowance n
  grind only [QInterval.width]

/-- Clamp an enlarged name to a nondegenerate closed rational domain. This
retains positive width even at either represented endpoint. -/
def clipped (a b : Rat) (x : RealCompute) : RealCompute where
  compute n :=
    { lo := if a≤((enlarged x).compute n).lo then ((enlarged x).compute n).lo else a
      hi := if ((enlarged x).compute n).hi≤b then ((enlarged x).compute n).hi else b }

theorem clipped_bounds (a b : Rat) (x : RealCompute) (n : Nat) :
    a≤((clipped a b x).compute n).lo ∧
    ((enlarged x).compute n).lo≤((clipped a b x).compute n).lo ∧
    ((clipped a b x).compute n).hi≤b ∧
    ((clipped a b x).compute n).hi≤((enlarged x).compute n).hi := by
  dsimp [clipped]
  grind

theorem clipped_positive {a b : Rat} {x : RealCompute} (hx : x.Valid) (hab : a<b)
    (ha : (RealCompute.ofRat a).Le x) (hb : x.Le (RealCompute.ofRat b)) (n : Nat) :
    ((clipped a b x).compute n).lo<((clipped a b x).compute n).hi := by
  have ho := hx.1 n
  have hp := allowance_pos n
  have hl := ha 0 n
  have hu := hb n 0
  change a≤(x.compute n).hi at hl
  change (x.compute n).lo≤b at hu
  dsimp [clipped,enlarged,QInterval.expand]
  grind [QInterval.width]

theorem clipped_equiv {a b : Rat} {x : RealCompute} (hx : x.Valid)
    (ha : (RealCompute.ofRat a).Le x) (hb : x.Le (RealCompute.ofRat b)) :
    (clipped a b x).Equiv x := by
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  have ho := hx.1 n
  have hp := allowance_pos n
  have hl := ha 0 n
  have hu := hb n 0
  change a≤(x.compute n).hi at hl
  change (x.compute n).lo≤b at hu
  change ((clipped a b x).compute n).lo≤(x.compute n).hi ∧
    (x.compute n).lo≤((clipped a b x).compute n).hi
  dsimp [clipped,enlarged,QInterval.expand]
  grind [QInterval.width]

theorem clipped_valid {a b : Rat} {x : RealCompute} (hx : x.Valid) (hab : a<b)
    (ha : (RealCompute.ofRat a).Le x) (hb : x.Le (RealCompute.ofRat b)) :
    (clipped a b x).Valid := by
  have he := enlarged_valid hx
  refine ⟨fun n => by have h := clipped_positive hx hab ha hb n; change 0≤_ - _; grind only,?_,?_⟩
  · intro n m hnm
    have hn := he.2.1 n m hnm
    have hp := clipped_positive hx hab ha hb m
    refine ⟨?_,Rat.le_of_lt hp,?_⟩
    · change (if _ then _ else _)≤(if _ then _ else _)
      split <;> split <;> grind only
    · change (if _ then _ else _)≤(if _ then _ else _)
      split <;> split <;> grind only
  · intro eps
    obtain ⟨N,hN⟩ := he.2.2 eps
    refine ⟨N,fun n hn => ?_⟩
    have h := hN n hn
    have bounds := clipped_bounds a b x n
    change ((clipped a b x).compute n).hi-((clipped a b x).compute n).lo≤eps.val
    grind only [QInterval.width]

theorem clipped_admissible {a b : Rat} {x : RealCompute} (hx : x.Valid) (hab : a<b)
    (ha : (RealCompute.ofRat a).Le x) (hb : x.Le (RealCompute.ofRat b)) :
    Admissible (fun r => a≤r ∧ r≤b) x (clipped a b x) := by
  refine ⟨hx,clipped_valid hx hab ha hb,clipped_equiv hx ha hb,fun n => ⟨clipped_positive hx hab ha hb n,?_⟩⟩
  intro r hl hu
  have bounds := clipped_bounds a b x n
  exact ⟨Rat.le_trans bounds.1 hl,Rat.le_trans hu bounds.2.2.1⟩

/-- Every admissible bracket eventually fits strictly inside any rational
neighborhood certified by one stage of the point's name. -/
theorem eventually_inside {domain : Rat → Prop} {x A : RealCompute}
    (hA : Admissible domain x A) {l r : Rat} {k : Nat}
    (hl : l<(x.compute k).lo) (hr : (x.compute k).hi<r) :
    ∃ N, ∀ n, N≤n → l<(A.compute n).lo ∧ (A.compute n).hi<r := by
  let gap := if (x.compute k).lo-l ≤ r-(x.compute k).hi then
    ((x.compute k).lo-l)/2 else (r-(x.compute k).hi)/2
  have hg : 0<gap := by
    dsimp [gap]; split
    · rw [Rat.div_def]; exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))
    · rw [Rat.div_def]; exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))
  obtain ⟨N,hN⟩ := hA.2.1.2.2 ⟨gap,hg⟩
  refine ⟨N,fun n hn => ?_⟩
  have hw := hN n hn
  have hov := (RealCompute.compareAt_overlap_iff A x n k).1
    (RealCompute.allStagesOverlap_of_equiv hA.2.1 hA.1 hA.2.2.1 n k)
  unfold QInterval.Overlaps at hov
  dsimp [gap] at hw
  split at hw <;> constructor <;> grind only [QInterval.width,Rat.div_def]

/-- The literal hull of two disjoint outer secants. -/
def outerDerivative (f : Rat → RealCompute) (l u v r : Nat → Rat)
    (prec : Nat → Nat) : RealCompute where
  compute n := QInterval.hull ((secant f (l n) (u n)).compute (prec n))
    ((secant f (v n) (r n)).compute (prec n))

/-- Finite secant order and validity of the actual outer-secant boxes prove
that their value is the derivative. No derivative identity is assumed. -/
theorem outerDerivative_hasDerivative {domain : Rat → Prop} {f : Rat → RealCompute}
    {x : RealCompute} (l u v r : Nat → Rat) (prec : Nat → Nat)
    (hx : x.Valid) (hf : ∀ t, domain t → (f t).Valid)
    (existsBracket : ∃ A, Admissible domain x A)
    (hd : (outerDerivative f l u v r prec).Valid)
    (points : ∀ n, domain (l n) ∧ domain (u n) ∧ domain (v n) ∧ domain (r n))
    (order : ∀ w a b z, domain w → domain a → domain b → domain z →
      w<a → a≤b → b<z → (secant f w a).Le (secant f b z))
    (neighborhood : ∀ n, l n<u n ∧ v n<r n ∧
      ∃ k, u n<(x.compute k).lo ∧ (x.compute k).hi<v n) :
    HasDerivativeAt domain f x (outerDerivative f l u v r prec) := by
  apply hasDerivative_iff_secantLimits.mpr
  refine ⟨hx,hd,hf,existsBracket,fun A hA => ⟨hd,secants_valid hf hA,?_⟩⟩
  intro m eps
  obtain ⟨hlu,hvr,k,huk,hkv⟩ := neighborhood m
  obtain ⟨N,hN⟩ := eventually_inside hA huk hkv
  refine ⟨N,fun n hn => ?_⟩
  have hi := hN n hn
  have hmem := hA.2.2.2 n
  have ha := hmem.2 _ (Rat.le_refl) (Rat.le_of_lt hmem.1)
  have hb := hmem.2 _ (Rat.le_of_lt hmem.1) (Rat.le_refl)
  have left := order (l m) (u m) (A.compute n).lo (A.compute n).hi
    (points m).1 (points m).2.1 ha hb hlu (Rat.le_of_lt hi.1) hmem.1
  have right := order (A.compute n).lo (A.compute n).hi (v m) (r m)
    ha hb (points m).2.2.1 (points m).2.2.2 hmem.1 (Rat.le_of_lt hi.2) hvr
  constructor
  · intro i j
    have h := left (prec m) j
    change ((outerDerivative f l u v r prec).compute m).lo - eps.val ≤
      ((secants f A n).compute j).hi
    dsimp [outerDerivative,QInterval.hull]
    have := eps.property
    grind [secants]
  · intro i j
    have h := right i (prec m)
    change ((secants f A n).compute i).lo ≤
      ((outerDerivative f l u v r prec).compute m).hi + eps.val
    dsimp [outerDerivative,QInterval.hull]
    have := eps.property
    grind [secants]


/-- A positive sequence can converge to the degenerate exact zero name. This
would fail under the unpadded target-box containment criterion. -/
theorem allowance_tendsTo_zero :
    RawLimit.TendsTo (fun n => RealCompute.ofRat (allowance n)) (RealCompute.ofRat 0) := by
  refine ⟨RealCompute.ofRat_valid 0,fun n => RealCompute.ofRat_valid _,?_⟩
  intro m eps
  obtain ⟨N,hN⟩ := allowance_shrinks eps
  refine ⟨N,fun n hn => ⟨?_,?_⟩⟩
  · intro _ _
    have hp := allowance_pos n
    have he := eps.property
    change (0:Rat)-eps.val≤allowance n
    grind only
  · intro _ _
    change allowance n≤(0:Rat)+eps.val
    simpa only [Rat.zero_add] using hN n hn

end ComputableAnalysis.BracketDerivative


