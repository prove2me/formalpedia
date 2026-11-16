-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ElementaryPowerSeries
-- name    : liuyao_ca_fd889115_k1_Analysis_ElementaryPowerSeries
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:08:24.848017+00:00
-- url     : https://prove2.me/theorems/2d2d122e-0d58-4f30-b687-adc835dd81b7
-- title:
--   Computable analysis · ElementaryPowerSeries · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ElementaryPowerSeries.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ElementaryRational
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientAlgebra

set_option autoImplicit true

/-! Certified rational elementary series with input-dependent tail schedules.
The finite odd/even prefixes are computed before stabilization; agreement is
proved by shared finite witnesses, rather than assumed in a function record. -/
namespace ComputableAnalysis.ElementaryPowerSeries
open ComplexCompute ComplexExponentialApproximation
set_option maxHeartbeats 1000000

theorem normBound_neg (z : QComplex) : QComplex.normBound (QComplex.neg z) = QComplex.normBound z := by
  simp only [QComplex.normBound,QComplex.neg,qabs_neg]

theorem exponentialPrefix_future {z : QComplex} {C : Rat} (hC : 0 ≤ C)
    (hz : QComplex.normBound z ≤ C) {first later : Nat} (hfl : first ≤ later) :
    (QBox.point (expPrefix z (RationalMajorant.factorialTailStart C + later))).NestedIn
      (QBox.expand (QBox.point (expPrefix z (RationalMajorant.factorialTailStart C + first)))
        (stageRadius C first)) := by
  let extra := later-first
  have hl : RationalMajorant.factorialTailStart C + later =
      (RationalMajorant.factorialTailStart C + first)+extra := by dsimp [extra]; omega
  have hp := expPrefix_add z (RationalMajorant.factorialTailStart C + first) extra
  rw [←hl] at hp
  have ht := tailPartial_normBound_le hC hz (RationalMajorant.factorialTailStart C + first) extra
  have hm := RationalMajorant.factorialTailPartial_bound hC
    (RationalMajorant.factorialTailStart_mono C _ first
      (RationalMajorant.factorialTailStart_satisfies C)) extra
  have he : QComplex.normBound (tailPartial z
      (RationalMajorant.factorialTailStart C + first) extra) ≤ stageRadius C first :=
    Rat.le_trans ht (by simpa [stageRadius] using hm)
  rw [hp]
  exact point_add_error_nested_expand _ _ he

theorem exponentialRaw_contains_future_prefix {z : QComplex} {C : Rat}
    (hC : 0 ≤ C) (hz : QComplex.normBound z ≤ C) {first later : Nat} (hfl : first ≤ later) :
    (QBox.point (expPrefix z (RationalMajorant.factorialTailStart C + later))).NestedIn
      ((exponentialRawAt z C).compute first) :=
  cauchyStabilize_contains_external (candidate := directCandidate z C)
    (radius := stageRadius C)
    (external := fun n => QBox.point (expPrefix z (RationalMajorant.factorialTailStart C+n)))
    (fun _ _ h => exponentialPrefix_future hC hz h) _ _ hfl

def pair (odd : Bool) (a b : QComplex) : QComplex :=
  QComplex.scaleRat (1/2) (if odd then QComplex.sub a b else QComplex.add a b)

def pairPrefix (odd : Bool) (z : QComplex) (terms : Nat) : QComplex :=
  pair odd (expPrefix z terms) (expPrefix (QComplex.neg z) terms)

def pairCandidate (odd : Bool) (z : QComplex) (C : Rat) : ComplexCompute where
  compute n := QBox.point (pairPrefix odd z (RationalMajorant.factorialTailStart C+n))

theorem pairCandidate_future {z : QComplex} {C : Rat} (hC : 0 ≤ C)
    (hz : QComplex.normBound z ≤ C) (odd : Bool) :
    ∀ first later, first ≤ later → ((pairCandidate odd z C).compute later).NestedIn
      (QBox.expand ((pairCandidate odd z C).compute first) (stageRadius C first)) := by
  intro first later hfl
  have ha := exponentialPrefix_future hC hz hfl
  have hb := exponentialPrefix_future hC (z := QComplex.neg z)
    (by rw [normBound_neg]; exact hz) hfl
  simp only [QBox.NestedIn,QBox.point,QBox.expand,QComplex.le_def,QComplex.neg] at ha hb
  change (QBox.point (pairPrefix odd z (RationalMajorant.factorialTailStart C+later))).NestedIn
    (QBox.expand (QBox.point (pairPrefix odd z (RationalMajorant.factorialTailStart C+first))) _)
  unfold pairPrefix pair
  cases odd <;> simp only [Bool.false_eq_true,if_false,if_true,QBox.NestedIn,
    QBox.point,QBox.expand,QComplex.scaleRat,QComplex.sub,QComplex.add,QComplex.neg,QComplex.le_def]
  all_goals constructor <;> constructor <;> grind only

def pairSeries (odd : Bool) (z : QComplex) : ComplexCompute :=
  cauchyStabilize (pairCandidate odd z (QComplex.normBound z)) (stageRadius (QComplex.normBound z))

theorem pairSeries_valid (odd : Bool) (z : QComplex) : (pairSeries odd z).Valid := by
  apply cauchyStabilize_valid
  · intro n; exact QComplex.le_refl _
  · intro eps; refine ⟨0,?_⟩; intro n _
    exact ⟨by simpa [pairCandidate,QBox.point,QBox.width,Rat.sub_self] using Rat.le_of_lt eps.property,
      by simpa [pairCandidate,QBox.point,QBox.height,Rat.sub_self] using Rat.le_of_lt eps.property⟩
  · exact pairCandidate_future (QComplex.normBound_nonneg z) Rat.le_refl odd
  · exact stageRadius_shrinks (QComplex.normBound_nonneg z)

def hyperbolicSineValue (z : QComplex) : ComplexCompute := pairSeries true z
def hyperbolicCosineValue (z : QComplex) : ComplexCompute := pairSeries false z
def sineValue (z : QComplex) : ComplexCompute :=
  mulI (neg (pairSeries true (QComplex.mul ElementaryRational.imaginaryUnit z)))
def cosineValue (z : QComplex) : ComplexCompute :=
  pairSeries false (QComplex.mul ElementaryRational.imaginaryUnit z)

theorem hyperbolicSineValue_valid (z : QComplex) : (hyperbolicSineValue z).Valid := pairSeries_valid _ _
theorem hyperbolicCosineValue_valid (z : QComplex) : (hyperbolicCosineValue z).Valid := pairSeries_valid _ _
theorem sineValue_valid (z : QComplex) : (sineValue z).Valid := mulI_valid (neg_valid (pairSeries_valid _ _))
theorem cosineValue_valid (z : QComplex) : (cosineValue z).Valid := pairSeries_valid _ _

def nativePair (odd : Bool) (z : QComplex) : ComplexCompute :=
  scaleRat (1/2) (if odd then sub (ElementaryRational.exponentialValue z)
    (ElementaryRational.exponentialValue (QComplex.neg z)) else
    add (ElementaryRational.exponentialValue z) (ElementaryRational.exponentialValue (QComplex.neg z)))

theorem nativePair_valid (odd : Bool) (z : QComplex) : (nativePair odd z).Valid := by
  unfold nativePair
  apply scaleRat_valid_of_nonneg (by decide +kernel)
  cases odd
  · exact add_valid (ElementaryRational.exponentialValue_valid _) (ElementaryRational.exponentialValue_valid _)
  · exact sub_valid (ElementaryRational.exponentialValue_valid _) (ElementaryRational.exponentialValue_valid _)

theorem pairSeries_agrees (odd : Bool) (z : QComplex) :
    (pairSeries odd z).Equiv (nativePair odd z) := by
  intro n
  let p := pairPrefix odd z (RationalMajorant.factorialTailStart (QComplex.normBound z)+n)
  have ha := exponentialRaw_contains_future_prefix (QComplex.normBound_nonneg z)
    (z := z) Rat.le_refl (Nat.le_refl n)
  have hb := exponentialRaw_contains_future_prefix (QComplex.normBound_nonneg z)
    (z := QComplex.neg z) (by rw [normBound_neg]; exact Rat.le_refl) (Nat.le_refl n)
  have hp := cauchyStabilize_contains_current
    (pairCandidate_future (QComplex.normBound_nonneg z) Rat.le_refl odd) n
  have hn : ((nativePair odd z).compute n).lo ≤ p ∧ p ≤ ((nativePair odd z).compute n).hi := by
    have ha' : ((ElementaryRational.exponentialValue z).compute n).lo ≤
        expPrefix z (RationalMajorant.factorialTailStart (QComplex.normBound z)+n) ∧
        expPrefix z (RationalMajorant.factorialTailStart (QComplex.normBound z)+n) ≤
          ((ElementaryRational.exponentialValue z).compute n).hi := ha
    have hb' : ((ElementaryRational.exponentialValue (QComplex.neg z)).compute n).lo ≤
        expPrefix (QComplex.neg z) (RationalMajorant.factorialTailStart (QComplex.normBound z)+n) ∧
        expPrefix (QComplex.neg z) (RationalMajorant.factorialTailStart (QComplex.normBound z)+n) ≤
          ((ElementaryRational.exponentialValue (QComplex.neg z)).compute n).hi := by
      simpa only [ElementaryRational.exponentialValue,normBound_neg,QBox.NestedIn,QBox.point] using hb
    cases odd
    · exact QBox.scaleRat_contains (QBox.add_contains ha'.1 ha'.2 hb'.1 hb'.2).1
        (QBox.add_contains ha'.1 ha'.2 hb'.1 hb'.2).2
    · have hs := QBox.add_contains ha'.1 ha'.2 (QBox.neg_contains hb').1 (QBox.neg_contains hb').2
      exact QBox.scaleRat_contains hs.1 hs.2
  apply (compareAt_overlap_iff _ _ n n).mpr
  exact QBox.overlaps_of_common_point hp hn

theorem rotation_half_equiv (z : ComplexCompute) (hz : z.Valid) :
    (mulI (neg (scaleRat (1/2) z))).Equiv (mul (ofQComplex ⟨0,-(1/2)⟩) z) := by
  intro n
  let p := (z.compute n).center
  have hp := QBox.center_mem (valid_ordered hz n)
  have hm := QBox.mul_contains (A := QBox.point ⟨0,-(1/2)⟩) (B := z.compute n)
    (z := ⟨0,-(1/2)⟩) (w := p) (QComplex.le_refl (⟨0,-(1/2)⟩ : QComplex))
    (QComplex.le_refl _) hp.1 hp.2
  apply (compareAt_overlap_iff _ _ n n).mpr
  apply QBox.overlaps_of_common_point (point := QComplex.mul ⟨0,-(1/2)⟩ p) _ hm
  simp only [mulI,neg,scaleRat,QBox.neg,QBox.scaleRat,Rat.neg_neg,
    if_pos (show (0:Rat) ≤ 1/2 by decide +kernel)]
  change (⟨(1/2)*(z.compute n).lo.im,-((1/2)*(z.compute n).hi.re)⟩ : QComplex) ≤
      QComplex.mul ⟨0,-(1/2)⟩ p ∧ QComplex.mul ⟨0,-(1/2)⟩ p ≤
      (⟨(1/2)*(z.compute n).hi.im,-((1/2)*(z.compute n).lo.re)⟩ : QComplex)
  simp only [QComplex.le_def,QComplex.mul,Rat.zero_mul,Rat.sub_eq_add_neg,Rat.zero_add]
  change (z.compute n).lo ≤ p ∧ p ≤ (z.compute n).hi at hp
  simp only [QComplex.le_def] at hp
  constructor <;> constructor <;> grind only

theorem sineValue_agrees (z : QComplex) : (sineValue z).Equiv (ElementaryRational.sineRadianValue z) := by
  unfold sineValue ElementaryRational.sineRadianValue
  apply equiv_trans (sineValue_valid z) (mulI_valid (neg_valid (nativePair_valid true _)))
    (ElementaryRational.sineRadianValue_valid z)
    (mulI_equiv (neg_equiv (pairSeries_agrees true _)))
  exact rotation_half_equiv _ (sub_valid (ElementaryRational.exponentialValue_valid _)
    (ElementaryRational.exponentialValue_valid _))

theorem cosineValue_agrees (z : QComplex) : (cosineValue z).Equiv (ElementaryRational.cosineRadianValue z) :=
  pairSeries_agrees false _
theorem hyperbolicSineValue_agrees (z : QComplex) :
    (hyperbolicSineValue z).Equiv (ElementaryRational.sinhValue z) := pairSeries_agrees true _
theorem hyperbolicCosineValue_agrees (z : QComplex) :
    (hyperbolicCosineValue z).Equiv (ElementaryRational.coshValue z) := pairSeries_agrees false _

def sine : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (sineValue z).compute
def cosine : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (cosineValue z).compute
def hyperbolicSine : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (hyperbolicSineValue z).compute
def hyperbolicCosine : FunctionRaw where
  domain := FunctionRaw.entire
  compute z _ := (hyperbolicCosineValue z).compute
theorem sine_valid : sine.Valid := fun z _ => sineValue_valid z
theorem cosine_valid : cosine.Valid := fun z _ => cosineValue_valid z
theorem hyperbolicSine_valid : hyperbolicSine.Valid := fun z _ => hyperbolicSineValue_valid z
theorem hyperbolicCosine_valid : hyperbolicCosine.Valid := fun z _ => hyperbolicCosineValue_valid z
theorem sine_agrees : sine.AgreeOnCommonDomain ElementaryRational.sineRadian :=
  fun z _ _ => sineValue_agrees z
theorem cosine_agrees : cosine.AgreeOnCommonDomain ElementaryRational.cosineRadian :=
  fun z _ _ => cosineValue_agrees z
theorem hyperbolicSine_agrees : hyperbolicSine.AgreeOnCommonDomain ElementaryRational.sinh :=
  fun z _ _ => hyperbolicSineValue_agrees z
theorem hyperbolicCosine_agrees : hyperbolicCosine.AgreeOnCommonDomain ElementaryRational.cosh :=
  fun z _ _ => hyperbolicCosineValue_agrees z

end ComputableAnalysis.ElementaryPowerSeries


