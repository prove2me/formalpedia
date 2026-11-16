-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralSpecification
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralSpecification
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:52:54.852971+00:00
-- url     : https://prove2.me/theorems/e8fce354-f1c1-4526-98c7-9916d7489177
-- title:
--   Computable analysis · IntegralSpecification · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralSpecification.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus

set_option autoImplicit true

/-!
# A checked rectangle-based integral relation

`Integral.HasIntegral F I` is the present rectangle-based sufficient route,
not the intended method-independent core and not a quadrature algorithm.
It says that the valid raw value `I` obeys every finite rational lower/upper
rectangle bound for `F`, and that these bounds can be arbitrarily tight.
Those tests are hypotheses of this route; they must not be made compulsory
for every new function-specific construction. There is no assertion that an
arbitrary interval function has an integral. See textbook/03-integrals.md.

Uniqueness is proved directly from the specification, without constructing or
selecting an integral. Existence proofs must separately certify their literal
computations. Rational endpoints do not restrict the values of the integrand
or the integral to rational numbers.
-/

namespace ComputableAnalysis
namespace Integral

/-- Literal finite rational summation; no limiting operation is involved. -/
def rectangleSum (term : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n+1 => rectangleSum term n + term n

theorem rectangleSum_mono (f g : Nat → Rat) (n : Nat)
    (h : ∀ k, k < n → f k ≤ g k) : rectangleSum f n ≤ rectangleSum g n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    exact rat_add_le_add (ih (fun k hk => h k (by omega))) (h n (by omega))

theorem rectangleSum_telescope (f : Nat → Rat) (n : Nat) :
    rectangleSum (fun k => f (k+1) - f k) n = f n - f 0 := by
  induction n with
  | zero => simp only [rectangleSum]; grind
  | succ n ih => simp only [rectangleSum, ih]; grind

theorem rectangleSum_scale (f : Nat → Rat) (c : Rat) (n : Nat) :
    rectangleSum (fun k => f k * c) n = rectangleSum f n * c := by
  induction n with
  | zero => simp [rectangleSum]
  | succ n ih => simp only [rectangleSum, ih]; grind

/-- Finite rational lower and upper functions on a rational partition.
Bounds concern represented values, not containment of every evaluator box.
Thus changing an evaluator or its precision schedule does not change them. -/
structure Bounds (F : FunctionOnInterval) where
  partition : RationalPartition F.lower F.upper
  lower : Nat → Rat
  upper : Nat → Rat
  lower_le : ∀ k (hk : k < partition.pieces) x
    (hx : (partition.cell k hk).contains x) n,
    lower k ≤ (F.compute x ((partition.cell k hk).contains_inDomain hx) n).hi
  upper_ge : ∀ k (hk : k < partition.pieces) x
    (hx : (partition.cell k hk).contains x) n,
    (F.compute x ((partition.cell k hk).contains_inDomain hx) n).lo ≤ upper k

namespace Bounds

def lowerSum {F : FunctionOnInterval} (B : Bounds F) : Rat :=
  rectangleSum
    (fun k => (B.partition.point (k+1) - B.partition.point k) * B.lower k)
    B.partition.pieces

def upperSum {F : FunctionOnInterval} (B : Bounds F) : Rat :=
  rectangleSum
    (fun k => (B.partition.point (k+1) - B.partition.point k) * B.upper k)
    B.partition.pieces

def Encloses {F : FunctionOnInterval} (B : Bounds F) (I : RealCompute) : Prop :=
  ∀ n, B.lowerSum ≤ (I.compute n).hi ∧ (I.compute n).lo ≤ B.upperSum

end Bounds

/-- Arbitrarily tight finite bounds. This is a proposition about the integrand,
not an integral evaluator, a chosen rate, or an existence axiom. -/
def HasTightBounds (F : FunctionOnInterval) : Prop :=
  ∀ eps : QPos, ∃ B : Bounds F, B.upperSum - B.lowerSum ≤ eps.val

/-- A supplied raw real is the definite integral on the function's rational
interval. Neither existence nor a preferred implementation is built in. -/
structure HasIntegral (F : FunctionOnInterval) (I : RealCompute) : Prop where
  valid : I.Valid
  bounds : ∀ B : Bounds F, B.Encloses I
  tight : HasTightBounds F

/-- Two values obeying the same arbitrarily tight rational bounds coincide.
This is a separation proof using rational arithmetic only. -/
theorem equiv_of_bounds {F : FunctionOnInterval} {I J : RealCompute}
    (htight : HasTightBounds F)
    (hI : ∀ B : Bounds F, B.Encloses I)
    (hJ : ∀ B : Bounds F, B.Encloses J) : I.Equiv J := by
  have hle : ∀ (X Y : RealCompute),
      (∀ B : Bounds F, B.Encloses X) →
      (∀ B : Bounds F, B.Encloses Y) → X.Le Y := by
    intro X Y hX hY n m
    by_cases h : (X.compute n).lo ≤ (Y.compute m).hi
    · exact h
    exfalso
    have hgap : 0 < ((X.compute n).lo - (Y.compute m).hi) / 2 := by grind
    obtain ⟨B, hB⟩ := htight ⟨_, hgap⟩
    have hx := (hX B n).2
    have hy := (hY B m).1
    change B.upperSum - B.lowerSum ≤
      ((X.compute n).lo - (Y.compute m).hi) / 2 at hB
    grind
  exact RealCompute.equiv_of_le_of_ge (hle I J hI hJ) (hle J I hJ hI)

/-- Uniqueness is independent of every existence theorem and every algorithm. -/
theorem HasIntegral.unique {F : FunctionOnInterval} {I J : RealCompute}
    (hI : HasIntegral F I) (hJ : HasIntegral F J) : I.Equiv J :=
  equiv_of_bounds hI.tight hI.bounds hJ.bounds

/-- The specification survives replacement by any equivalent valid raw name. -/
theorem HasIntegral.congr {F : FunctionOnInterval} {I J : RealCompute}
    (hI : HasIntegral F I) (hJ : J.Valid) (heq : I.Equiv J) :
    HasIntegral F J := by
  refine ⟨hJ, ?_, hI.tight⟩
  intro B n
  have hlow : (RealCompute.ofRat B.lowerSum).Le I := fun _ m => (hI.bounds B m).1
  have hupp : I.Le (RealCompute.ofRat B.upperSum) := fun m _ => (hI.bounds B m).2
  exact ⟨RealCompute.le_trans hI.valid hlow (RealCompute.le_of_equiv hI.valid hJ heq) 0 n,
    RealCompute.le_trans hI.valid (RealCompute.le_of_equiv hJ hI.valid
      (RealCompute.equiv_symm heq)) hupp n 0⟩

/-- A checked construction packages a supplied candidate with its semantic
proof. Constructing this object proves existence for this particular function.
Executability of the supplied program is a separate property: a `RealCompute`
field alone is not a computability certificate. -/
structure Certified (F : FunctionOnInterval) where
  value : RealCompute
  isIntegral : HasIntegral F value

theorem Certified.valid {F : FunctionOnInterval} (c : Certified F) :
    c.value.Valid := c.isIntegral.valid

theorem Certified.unique {F : FunctionOnInterval} (c d : Certified F) :
    c.value.Equiv d.value := c.isIntegral.unique d.isIntegral

/-- Public integral constructions include a proof of the mathematical role.
Validity-only algorithms live in `CandidateConstructionFor`. -/
abbrev ConstructionFor := Certified

def integralFor (F : FunctionOnInterval) (c : ConstructionFor F) : RealCompute := c.value

theorem integralFor_valid (F : FunctionOnInterval) (c : ConstructionFor F) :
    (integralFor F c).Valid := c.valid

theorem integralFor_hasIntegral (F : FunctionOnInterval) (c : ConstructionFor F) :
    HasIntegral F (integralFor F c) := c.isIntegral

theorem integralFor_unique (F : FunctionOnInterval) (c d : ConstructionFor F) :
    (integralFor F c).Equiv (integralFor F d) := c.unique d

/-- Extensional equality of represented integrands on the same rational domain. -/
structure SameValues (F G : FunctionOnInterval) : Prop where
  lower : F.lower = G.lower
  upper : F.upper = G.upper
  values : ∀ x (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval G.lower G.upper x),
    RealCompute.Equiv { compute := F.compute x hx } { compute := G.compute x hy }

theorem SameValues.symm {F G : FunctionOnInterval} (h : SameValues F G) :
    SameValues G F := ⟨h.lower.symm, h.upper.symm,
      fun x hx hy => RealCompute.equiv_symm (h.values x hy hx)⟩

/-- Bounds use value order and hence transport between independent evaluators. -/
def Bounds.transport {F G : FunctionOnInterval} (B : Bounds F)
    (h : SameValues F G) : Bounds G where
  partition := { B.partition with
    left_endpoint := B.partition.left_endpoint.trans h.lower
    right_endpoint := B.partition.right_endpoint.trans h.upper }
  lower := B.lower
  upper := B.upper
  lower_le := by
    intro k hk x hx n
    let hxF := (B.partition.cell k hk).contains_inDomain hx
    let hxG : inDomainInterval G.lower G.upper x := by
      simpa [← h.lower, ← h.upper] using hxF
    let X : RealCompute := { compute := F.compute x hxF }
    let Y : RealCompute := { compute := G.compute x hxG }
    have hX : X.Valid := F.valid_on x (F.defined_on x hxF)
    have hY : Y.Valid := G.valid_on x (G.defined_on x hxG)
    have hl : (RealCompute.ofRat (B.lower k)).Le X := fun _ m => B.lower_le k hk x hx m
    exact RealCompute.le_trans hX hl (RealCompute.le_of_equiv hX hY (h.values x hxF hxG)) 0 n
  upper_ge := by
    intro k hk x hx n
    let hxF := (B.partition.cell k hk).contains_inDomain hx
    let hxG : inDomainInterval G.lower G.upper x := by
      simpa [← h.lower, ← h.upper] using hxF
    let X : RealCompute := { compute := F.compute x hxF }
    let Y : RealCompute := { compute := G.compute x hxG }
    have hX : X.Valid := F.valid_on x (F.defined_on x hxF)
    have hY : Y.Valid := G.valid_on x (G.defined_on x hxG)
    have hu : X.Le (RealCompute.ofRat (B.upper k)) := fun m _ => B.upper_ge k hk x hx m
    exact RealCompute.le_trans hX
      (RealCompute.le_of_equiv hY hX (RealCompute.equiv_symm (h.values x hxF hxG))) hu n 0

/-- Integrals depend on values of the integrand, not its interval program. -/
theorem HasIntegral.congrFunction {F G : FunctionOnInterval} {I : RealCompute}
    (hI : HasIntegral F I) (h : SameValues F G) : HasIntegral G I := by
  refine ⟨hI.valid, fun B => hI.bounds (B.transport h.symm), ?_⟩
  intro eps
  obtain ⟨B, hB⟩ := hI.tight eps
  exact ⟨B.transport h, hB⟩

/-- Promote a numerical candidate only after its independent semantic proof.
This is an adapter, not an existence or FTC theorem. -/
def CandidateConstructionFor.certify {F : FunctionOnInterval}
    (c : CandidateConstructionFor F) (h : HasIntegral F (candidateValueFor F c)) :
    ConstructionFor F := ⟨candidateValueFor F c, h⟩

/-- A constant with an arbitrary valid represented value, including irrational
values. Only the endpoints and the finite partition arithmetic are rational. -/
def constant (c : RealCompute) (hc : c.Valid) (a b : Rat) : FunctionOnInterval where
  raw := { definedAt := fun _ => True, compute := fun _ _ => c.compute }
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := fun _ _ => hc

theorem Bounds.constant_encloses {c : RealCompute} {hc : c.Valid} {a b : Rat}
    (hab : a ≤ b) (B : Bounds (constant c hc a b)) :
    B.Encloses (RealCompute.scaleRat (b-a) c) := by
  intro n
  have hlength : 0 ≤ b-a := by grind
  have hlo := rectangleSum_mono
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.lower k)
    (fun k => (B.partition.point (k+1)-B.partition.point k)*(c.compute n).hi)
    B.partition.pieces (by
      intro k hk
      have hm := B.partition.monotone k (k+1) (by omega) (by omega)
      have hb := B.lower_le k hk (B.partition.point k) ⟨Rat.le_refl, hm⟩ n
      exact Rat.mul_le_mul_of_nonneg_left hb (by grind))
  have hhi := rectangleSum_mono
    (fun k => (B.partition.point (k+1)-B.partition.point k)*(c.compute n).lo)
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.upper k)
    B.partition.pieces (by
      intro k hk
      have hm := B.partition.monotone k (k+1) (by omega) (by omega)
      have hb := B.upper_ge k hk (B.partition.point k) ⟨Rat.le_refl, hm⟩ n
      exact Rat.mul_le_mul_of_nonneg_left hb (by grind))
  rw [rectangleSum_scale, rectangleSum_telescope,
    B.partition.left_endpoint, B.partition.right_endpoint] at hlo hhi
  simpa [Bounds.Encloses, Bounds.lowerSum, Bounds.upperSum, constant,
    RealCompute.scaleRat, RealCompute.scaleRatCompute, hlength] using And.intro hlo hhi

def constantBounds (c : RealCompute) (hc : c.Valid) (a b : Rat)
    (hab : a ≤ b) (stage : Nat) : Bounds (constant c hc a b) where
  partition := RationalPartition.uniform a b 1 (by decide) hab
  lower := fun _ => (c.compute stage).lo
  upper := fun _ => (c.compute stage).hi
  lower_le := by
    intro k hk x hx n
    exact RealCompute.le_refl c hc stage n
  upper_ge := by
    intro k hk x hx n
    exact RealCompute.le_refl c hc n stage

theorem constantBounds_gap (c : RealCompute) (hc : c.Valid) (a b : Rat)
    (hab : a ≤ b) (stage : Nat) :
    (constantBounds c hc a b hab stage).upperSum -
      (constantBounds c hc a b hab stage).lowerSum =
      (b-a)*(c.compute stage).width := by
  simp only [Bounds.lowerSum, Bounds.upperSum, constantBounds]
  rw [rectangleSum_scale, rectangleSum_scale,
    rectangleSum_telescope]
  simp only [RationalPartition.uniform, leftPoint_zero, leftPoint_endpoint (by decide : 0 < 1)]
  grind [QInterval.width]

/-- A genuine existence example: constants of arbitrary represented value. -/
theorem constant_hasIntegral (c : RealCompute) (hc : c.Valid) (a b : Rat)
    (hab : a ≤ b) :
    HasIntegral (constant c hc a b) (RealCompute.scaleRat (b-a) c) := by
  refine ⟨RealCompute.scaleRat_valid hc, fun B => B.constant_encloses hab, ?_⟩
  intro eps
  have hd : 0 < b-a+1 := by grind
  have he : 0 < eps.val/(b-a+1) := by
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hd)
  obtain ⟨N, hN⟩ := hc.2.2 ⟨_, he⟩
  refine ⟨constantBounds c hc a b hab N, ?_⟩
  rw [constantBounds_gap]
  have hw := hN N (Nat.le_refl _)
  have hw0 := hc.1 N
  have hm := Rat.mul_le_mul_of_nonneg_left hw (Rat.le_of_lt hd)
  have hcanc : (b-a+1)*(eps.val/(b-a+1)) = eps.val := by
    rw [Rat.div_def]
    have hi := Rat.mul_inv_cancel (b-a+1) (Rat.ne_of_gt hd)
    grind
  change (b-a+1)*(c.compute N).width ≤ (b-a+1)*(eps.val/(b-a+1)) at hm
  rw [hcanc] at hm
  grind

/-- Conditional FTC for an exact rational endpoint expression. The supplied
cell-order evidence is about finite derivative bounds and endpoint increments;
the integral in the conclusion is any supplied witness of the specification. -/
theorem ExactCellOrderPreservation.encloses {f P : Rat → Rat} {a b : Rat}
    (hP : ExactCellOrderPreservation f (fun u v => P v - P u) a b) :
    ∀ B : Bounds (FunctionOnInterval.exactRat f a b),
      B.Encloses (RealCompute.ofRat (P b-P a)) := by
  intro B n
  have hlo := rectangleSum_mono
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.lower k)
    (fun k => P (B.partition.point (k+1))-P (B.partition.point k))
    B.partition.pieces (by
      intro k hk
      let hcell := B.partition.cell k hk
      exact hP.lower_const hcell.lower_mem hcell.ordered hcell.upper_mem
        (fun {x} hx hy => B.lower_le k hk x ⟨hx, hy⟩ 0))
  have hhi := rectangleSum_mono
    (fun k => P (B.partition.point (k+1))-P (B.partition.point k))
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.upper k)
    B.partition.pieces (by
      intro k hk
      let hcell := B.partition.cell k hk
      exact hP.upper_const hcell.lower_mem hcell.ordered hcell.upper_mem
        (fun {x} hx hy => B.upper_ge k hk x ⟨hx, hy⟩ 0))
  rw [rectangleSum_telescope (fun k => P (B.partition.point k)), B.partition.left_endpoint,
    B.partition.right_endpoint] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem HasIntegral.ftc_exact {f P : Rat → Rat} {a b : Rat} {I : RealCompute}
    (hI : HasIntegral (FunctionOnInterval.exactRat f a b) I)
    (hP : ExactCellOrderPreservation f (fun u v => P v - P u) a b) :
    I.Equiv (RealCompute.ofRat (P b-P a)) :=
  equiv_of_bounds hI.tight hI.bounds hP.encloses

/-- Existence for an exact endpoint algorithm is separate from the FTC law. -/
theorem ExactCellOrderPreservation.hasIntegral {f P : Rat → Rat} {a b : Rat}
    (hP : ExactCellOrderPreservation f (fun u v => P v - P u) a b)
    (htight : HasTightBounds (FunctionOnInterval.exactRat f a b)) :
    HasIntegral (FunctionOnInterval.exactRat f a b) (RealCompute.ofRat (P b-P a)) :=
  ⟨RealCompute.ofRat_valid _, hP.encloses, htight⟩

/-- Rational constants are one instance of the represented-constant theorem. -/
theorem exactRat_constant_hasIntegral (c a b : Rat) (hab : a ≤ b) :
    HasIntegral (FunctionOnInterval.exactRat (fun _ => c) a b)
      (RealCompute.ofRat ((b-a)*c)) := by
  have h0 := constant_hasIntegral (RealCompute.ofRat c) (RealCompute.ofRat_valid c) a b hab
  have h := h0.congrFunction (G := FunctionOnInterval.exactRat (fun _ => c) a b)
      ⟨rfl, rfl, fun _ _ _ => RealCompute.equiv_refl (RealCompute.ofRat c) (RealCompute.ofRat_valid c)⟩
  apply h.congr (J := RealCompute.ofRat ((b-a)*c)) (RealCompute.ofRat_valid ((b-a)*c))
  intro n
  apply (RealCompute.compareAt_overlap_iff _ _ n n).2
  have hlength : 0 ≤ b-a := by grind
  simp [RealCompute.scaleRat, RealCompute.scaleRatCompute, RealCompute.ofRat,
    hlength, QInterval.Overlaps]

/-- The existing constant algorithm has its semantic proof, independently of
its numerical validity certificate. -/
theorem constant_candidate_hasIntegral (c a b : Rat) (hab : a ≤ b) :
    HasIntegral (FunctionOnInterval.exactRat (fun _ => c) a b)
      (monotoneCandidateValueFor _ (constantMonotoneCandidateConstructionFor c a b)) :=
  exactRat_constant_hasIntegral c a b hab

/-! The following are mathematical law statements over supplied integral
witnesses. They replace the old (false) universal statements over arbitrary
valid numerical candidates. These declarations specify the laws; IntegralLaws
supplies their proofs at the present rectangle-based scope. -/

def LinearFor : Prop :=
  ∀ (F G H : FunctionOnInterval), F.PointwiseAdd G H →
    ∀ I J K, HasIntegral F I → HasIntegral G J → HasIntegral H K →
      K.Equiv (I+J)

def CompatibleWithScaleRatFor : Prop :=
  ∀ (r : Rat) (F G : FunctionOnInterval), F.PointwiseScaleRat r G →
    ∀ I J, HasIntegral F I → HasIntegral G J → J.Equiv (RealCompute.scaleRat r I)

def OrderPreservingFor : Prop :=
  ∀ (F G : FunctionOnInterval), F.PointwiseLe G →
    ∀ I J, HasIntegral F I → HasIntegral G J → I.Le J

def AdditiveOnAdjacentIntervalsFor : Prop :=
  ∀ (F : FunctionOnInterval) (a b c : Rat)
    (ha : F.lower ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ F.upper)
    (I J K : RealCompute),
    HasIntegral (F.restrict a b ha hab (Rat.le_trans hbc hc)) I →
    HasIntegral (F.restrict b c (Rat.le_trans ha hab) hbc hc) J →
    HasIntegral (F.restrict a c ha (Rat.le_trans hab hbc) hc) K → K.Equiv (I+J)

abbrev Linear := LinearFor
abbrev CompatibleWithScaleRat := CompatibleWithScaleRatFor
abbrev AdditiveOnAdjacentIntervals := AdditiveOnAdjacentIntervalsFor
abbrev PiecewiseMonotoneLinearFor := LinearFor
abbrev PiecewiseMonotoneCompatibleWithScaleRatFor := CompatibleWithScaleRatFor
abbrev PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor := AdditiveOnAdjacentIntervalsFor
abbrev PiecewiseMonotoneOrderPreservingFor := OrderPreservingFor

end Integral
end ComputableAnalysis


