-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ParametrizedContinuity
-- name    : liuyao_ca_fd889115_k1_Analysis_ParametrizedContinuity
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:56:55.090413+00:00
-- url     : https://prove2.me/theorems/0126813f-3e47-49ea-9b34-3be637b3f1d5
-- title:
--   Computable analysis · ParametrizedContinuity · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ParametrizedContinuity.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BracketDerivativeConstruction

set_option autoImplicit true

/-! Continuity from covered, valid parametrized output enclosures. Rational
inputs stay primary. Whole bracket images, rather than endpoint hulls, are
covered; all admissible brackets must give the same represented value. -/
namespace ComputableAnalysis.BracketContinuity
open RawLimit BracketDerivative
set_option maxHeartbeats 2000000

def observations (f : Rat → RealCompute) (A : RealCompute) (n : Nat) (y : RealCompute) : Prop :=
  ∃ r, (A.compute n).lo ≤ r ∧ r ≤ (A.compute n).hi ∧ y = f r

theorem observations_antitone {f : Rat → RealCompute} {A : RealCompute} (hA : A.Valid) :
    ∀ i j, i ≤ j → ∀ y, observations f A j y → observations f A i y := by
  rintro i j hij y ⟨r,hl,hr,rfl⟩
  have hn := hA.2.1 i j hij
  exact ⟨r,Rat.le_trans hn.1 hl,Rat.le_trans hr hn.2.2,rfl⟩

theorem observations_inhabited {domain : Rat → Prop} {f : Rat → RealCompute} {x A : RealCompute}
    (hf : ∀ r, domain r → (f r).Valid) (hA : Admissible domain x A) :
    ∀ n, ∃ y, y.Valid ∧ observations f A n y := by
  intro n
  have h := hA.2.2.2 n
  exact ⟨f (A.compute n).lo,hf _ (h.2 _ Rat.le_refl (Rat.le_of_lt h.1)),
    (A.compute n).lo,Rat.le_refl,Rat.le_of_lt h.1,rfl⟩

/-- The output value is specified by a valid covered diagonal for every
admissible input name. The inhabited family prevents vacuous continuity. -/
def HasContinuousAt (domain : Rat → Prop) (f : Rat → RealCompute) (x c : RealCompute) : Prop :=
  x.Valid ∧ c.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
  (∃ A, Admissible domain x A) ∧
  ∀ A, Admissible domain x A → HasEnclosureValue (observations f A) c

theorem unique {domain : Rat → Prop} {f : Rat → RealCompute} {x c d : RealCompute}
    (hc : HasContinuousAt domain f x c) (hd : HasContinuousAt domain f x d) : c.Equiv d := by
  obtain ⟨A,hA⟩ := hc.2.2.2.1
  exact HasEnclosureValue.unique (observations_antitone hA.2.1)
    (observations_inhabited hc.2.2.1 hA) (hc.2.2.2.2 A hA) (hd.2.2.2.2 A hA)

/-- Independently constructed bracket images agree. A rational point in the
intersection of two input boxes supplies the comparison; no output equality
or continuous extension is assumed. -/
theorem bracket_values_equiv {domain : Rat → Prop} {f : Rat → RealCompute}
    {x A B c d : RealCompute} (hf : ∀ r, domain r → (f r).Valid)
    (hA : Admissible domain x A) (hB : Admissible domain x B)
    (hc : HasEnclosureValue (observations f A) c)
    (hd : HasEnclosureValue (observations f B) d) : c.Equiv d := by
  obtain ⟨vc,Q,n,m,_,_,vC,eC,bC⟩ := hc
  obtain ⟨vd,R,p,q,_,_,vD,eD,bD⟩ := hd
  have eAB := RealCompute.equiv_trans hA.2.1 hA.1 hB.2.1 hA.2.2.1
    (RealCompute.equiv_symm hB.2.2.1)
  have eq : (diagonal Q n m).Equiv (diagonal R p q) := by
    intro k
    have ov := (RealCompute.compareAt_overlap_iff A B (n k) (p k)).mp
      (RealCompute.allStagesOverlap_of_equiv hA.2.1 hB.2.1 eAB (n k) (p k))
    let r := max (A.compute (n k)).lo (B.compute (p k)).lo
    have bounds : (A.compute (n k)).lo ≤ r ∧ r ≤ (A.compute (n k)).hi ∧
        (B.compute (p k)).lo ≤ r ∧ r ≤ (B.compute (p k)).hi := by
      have a := RealCompute.interval_order_of_valid A hA.2.1 (n k)
      have b := RealCompute.interval_order_of_valid B hB.2.1 (p k)
      unfold QInterval.Overlaps at ov
      dsimp [r]
      grind
    have vy := hf r ((hA.2.2.2 (n k)).2 r bounds.1 bounds.2.1)
    have a := bC k (f r) ⟨r,bounds.1,bounds.2.1,rfl⟩
    have b := bD k (f r) ⟨r,bounds.2.2.1,bounds.2.2.2,rfl⟩
    apply (RealCompute.compareAt_overlap_iff _ _ k k).mpr
    exact ⟨RealCompute.le_trans vy a.1 b.2 0 0,RealCompute.le_trans vy b.1 a.2 0 0⟩
  exact RealCompute.equiv_trans vc vC vd (RealCompute.equiv_symm eC)
    (RealCompute.equiv_trans vC vD vd eq eD)

/-- Function-specific bracket constructions suffice to construct a common
extension value. Agreement is proved by the preceding finite comparison. -/
theorem exists_continuousAt_of_enclosures {domain : Rat → Prop} {f : Rat → RealCompute}
    {x : RealCompute} (hx : x.Valid) (hf : ∀ r, domain r → (f r).Valid)
    (hbracket : ∃ A, Admissible domain x A)
    (construct : ∀ A, Admissible domain x A → ∃ c, HasEnclosureValue (observations f A) c) :
    ∃ c, HasContinuousAt domain f x c := by
  obtain ⟨A,hA⟩ := hbracket
  obtain ⟨c,hc⟩ := construct A hA
  refine ⟨c,hx,hc.1,hf,⟨A,hA⟩,fun B hB => ?_⟩
  obtain ⟨d,hd⟩ := construct B hB
  exact HasEnclosureValue.congr_value hd hc.1
    (bracket_values_equiv hf hB hA hd hc)

theorem congr_point {domain : Rat → Prop} {f : Rat → RealCompute} {x y c : RealCompute}
    (h : HasContinuousAt domain f x c) (hy : y.Valid) (hxy : x.Equiv y) :
    HasContinuousAt domain f y c := by
  refine ⟨hy,h.2.1,h.2.2.1,?_,?_⟩
  · obtain ⟨A,hA⟩ := h.2.2.2.1
    exact ⟨A,(admissible_congr h.1 hy hxy).mp hA⟩
  · intro A hA
    exact h.2.2.2.2 A ((admissible_congr h.1 hy hxy).mpr hA)

theorem congr_value {domain : Rat → Prop} {f : Rat → RealCompute} {x c d : RealCompute}
    (h : HasContinuousAt domain f x c) (hd : d.Valid) (hcd : c.Equiv d) :
    HasContinuousAt domain f x d :=
  ⟨h.1,hd,h.2.2.1,h.2.2.2.1,fun A hA =>
    HasEnclosureValue.congr_value (h.2.2.2.2 A hA) hd hcd⟩

theorem congr_function {domain : Rat → Prop} {f g : Rat → RealCompute} {x c : RealCompute}
    (h : HasContinuousAt domain f x c) (hg : ∀ r, domain r → (g r).Valid)
    (hfg : ∀ r, domain r → (f r).Equiv (g r)) :
    HasContinuousAt domain g x c := by
  refine ⟨h.1,h.2.1,hg,h.2.2.2.1,fun A hA => ?_⟩
  obtain ⟨hc,Q,n,m,hn,hm,hC,hCc,cover⟩ := h.2.2.2.2 A hA
  refine ⟨hc,Q,n,m,hn,hm,hC,hCc,?_⟩
  rintro k y ⟨r,hl,hr,rfl⟩
  have hd := (hA.2.2.2 (n k)).2 r hl hr
  exact inInterval_congr (h.2.2.1 r hd) (hg r hd) (hfg r hd)
    (cover k (f r) ⟨r,hl,hr,rfl⟩)

/-- Exact target-box agreement is a consequence, not a field of the
continuity predicate: every rational value in sufficiently small brackets
lies in every requested target box with an arbitrarily small allowance. -/
theorem hasContinuousAt_iff_neighborhoods {domain : Rat → Prop} {f : Rat → RealCompute}
    {x c : RealCompute} : HasContinuousAt domain f x c ↔
    x.Valid ∧ c.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
    (∃ A, Admissible domain x A) ∧
    ∀ A, Admissible domain x A → NeighborhoodTendsTo (observations f A) c := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun A hA =>
      (enclosureValue_iff (observations_antitone hA.2.1)).mp (h.2.2.2.2 A hA)⟩
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun A hA =>
      (enclosureValue_iff (observations_antitone hA.2.1)).mpr (h.2.2.2.2 A hA)⟩

/-- Every rational sample inside the shrinking input brackets has the same
limit. This consequence quantifies over all samples; none is preferred. -/
theorem values_tendTo {domain : Rat → Prop} {f : Rat → RealCompute} {x c A : RealCompute}
    (h : HasContinuousAt domain f x c) (hA : Admissible domain x A)
    (r : Nat → Rat) (hr : ∀ n, (A.compute n).lo ≤ r n ∧ r n ≤ (A.compute n).hi) :
    TendsTo (fun n => f (r n)) c := by
  have hn := (enclosureValue_iff (observations_antitone hA.2.1)).mp (h.2.2.2.2 A hA)
  refine ⟨h.2.1,fun n => h.2.2.1 _ ((hA.2.2.2 n).2 _ (hr n).1 (hr n).2),?_⟩
  intro k eps
  obtain ⟨N,hN⟩ := hn.2 k eps
  exact ⟨N,fun n hnn => hN _ (observations_antitone hA.2.1 N n hnn _
    ⟨r n,(hr n).1,(hr n).2,rfl⟩)⟩

theorem rational_agreement {domain : Rat → Prop} {f : Rat → RealCompute} {r : Rat} {c : RealCompute}
    (h : HasContinuousAt domain f (RealCompute.ofRat r) c) (hr : domain r) : c.Equiv (f r) := by
  obtain ⟨A,hA⟩ := h.2.2.2.1
  have bounds : ∀ n, (A.compute n).lo ≤ r ∧ r ≤ (A.compute n).hi := by
    intro n
    exact (RealCompute.compareAt_overlap_iff A (RealCompute.ofRat r) n n).mp (hA.2.2.1 n)
  exact RealCompute.equiv_symm (RawLimit.unique (RawLimit.constant (f r) (h.2.2.1 r hr))
    (values_tendTo h hA (fun _ => r) bounds))

theorem identity {domain : Rat → Prop} {x : RealCompute} (hx : x.Valid)
    (hbracket : ∃ A, Admissible domain x A) :
    HasContinuousAt domain RealCompute.ofRat x x := by
  refine ⟨hx,hx,fun r _ => RealCompute.ofRat_valid r,hbracket,fun A hA => ?_⟩
  refine ⟨hx,(fun n _ => A.compute n),(fun k => k),(fun k => k),
    cofinal_id,cofinal_id,hA.2.1,hA.2.2.1,?_⟩
  rintro k y ⟨r,hl,hr,rfl⟩
  exact ⟨fun _ _ => hl,fun _ _ => hr⟩

theorem constant {domain : Rat → Prop} {x c : RealCompute} (hx : x.Valid) (hc : c.Valid)
    (hbracket : ∃ A, Admissible domain x A) :
    HasContinuousAt domain (fun _ => c) x c := by
  refine ⟨hx,hc,fun _ _ => hc,hbracket,fun A _ => ?_⟩
  refine ⟨hc,(fun _ m => c.compute m),(fun k => k),(fun k => k),
    cofinal_id,cofinal_id,hc,RealCompute.equiv_refl _ hc,?_⟩
  rintro k y ⟨r,_,_,hy⟩
  rw [hy]
  exact ⟨fun _ j => RealCompute.le_refl c hc k j,
    fun i _ => RealCompute.le_refl c hc i k⟩

end ComputableAnalysis.BracketContinuity


