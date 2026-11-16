-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_ClassicalHuygens
-- name    : liuyao_ca_fd889115_k1_Distributions_ClassicalHuygens
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:40:36.368915+00:00
-- url     : https://prove2.me/theorems/b4f00365-bf2e-43c0-9c9b-f96384befcff
-- title:
--   Computable analysis · ClassicalHuygens · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/ClassicalHuygens.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_ForcedWaveTargets

set_option autoImplicit true

/-! Domain of dependence of an ordinary wave solution. The proof-facing
lemmas use the retarded kernel, but the milestone itself uses only functions. -/

open ComputableAnalysis

namespace ComputableDistributions.ClassicalHuygens

set_option maxHeartbeats 2000000

def close {d : Nat} (r : Rat) (p x : QPoint d) : Prop :=
  ∀ i, p i ≤ x i + r ∧ x i ≤ p i + r

def backwardBoundary {n : Nat} (q p : QPoint (n + 1)) : Prop :=
  OnForwardLightCone (spatialDimension := n) (fun i => p i - q i)

def onTimeZero {n : Nat} (x : QPoint n) : QPoint (n + 1) := Fin.cases 0 x

/-- A uniform neighborhood of the observation has no null connection
to a nonzero data value. Forcing times are restricted to the causal problem. -/
def DataVanishNearBackwardBoundary {n : Nat} (a b : TestFunction n)
    (f : TestFunction (n + 1)) (p : QPoint (n + 1)) (r : Rat) : Prop :=
  (∀ x z, close r p z → backwardBoundary (onTimeZero x) z →
    (a.value x).Equiv (RealCompute.ofRat 0) ∧ (b.value x).Equiv (RealCompute.ofRat 0)) ∧
  ∀ q z, 0 ≤ q (timeCoordinate n) → close r p z → backwardBoundary q z →
    (f.value q).Equiv (RealCompute.ofRat 0)

/-- An ordinary twice differentiable wave solution, sampled on rational
coordinates. Local joint Lipschitz bounds certify the continuous extension of
the values and the first two coordinate derivatives on boxes. -/
structure ClassicalSolution (n : Nat) where
  derivative : MultiIndex (n + 1) → QPoint (n + 1) → RealCompute
  valid : ∀ alpha p, (derivative alpha p).Valid
  localControl : ∀ (alpha : MultiIndex (n + 1)) (B : RationalBox (n + 1)),
    multiIndexOrder alpha ≤ 2 →
    ∃ C : Rat, 0 ≤ C ∧ ∀ p q, B.Contains p → B.Contains q →
      ∀ r : Rat, 0 ≤ r → close r p q →
        RealApproximationOrder.Small (RealApproximationOrder.sub
          (RealApproximationOrder.parameter (derivative alpha p) (valid alpha p))
          (RealApproximationOrder.parameter (derivative alpha q) (valid alpha q))) (C * r)
  nextPartial : ∀ alpha, multiIndexOrder alpha < 2 → ∀ i p,
    BracketDerivative.HasDerivativeAt (fun _ => True)
      (fun r => derivative alpha (replaceCoordinate p i r)) (RealCompute.ofRat (p i))
      (derivative (incrementIndex alpha i) p)

def ClassicalSolution.value {n : Nat} (u : ClassicalSolution n) (p : QPoint (n + 1)) :
    RealCompute := u.derivative (zeroIndex _) p

def Solves {n : Nat} (u : ClassicalSolution n) (a b : TestFunction n)
    (f : TestFunction (n + 1)) : Prop :=
  (∀ x, (u.value (onTimeZero x)).Equiv (a.value x) ∧
    (u.derivative (incrementIndex (zeroIndex _) (timeCoordinate n)) (onTimeZero x)).Equiv
      (b.value x)) ∧
  ∀ p, 0 < p (timeCoordinate n) →
    let second := fun i => u.derivative (incrementIndex (incrementIndex (zeroIndex _) i) i) p
    (RealCompute.sub (second (timeCoordinate n))
      (sumRaw n (fun i => second (spatialCoordinate i)))).Equiv (f.value p)

/-- A perturbation with no null connection to the observation leaves the
solution value unchanged. State this as the zero-response property, with
the data and solution denoting the differences of two experiments. -/
def Target : Prop :=
  ∀ n : Nat, 3 ≤ n → n % 2 = 1 →
    ∀ (a b : TestFunction n) (f : TestFunction (n + 1)) (u : ClassicalSolution n),
      Solves u a b f → ∀ p, 0 < p (timeCoordinate n) →
      (∃ r : Rat, 0 < r ∧ DataVanishNearBackwardBoundary a b f p r) →
      (u.value p).Equiv (RealCompute.ofRat 0)

private theorem zeroValid : (RealCompute.ofRat 0).Valid := RealCompute.ofRat_valid 0

private theorem raw_mul_zero {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (hz : y.Equiv (RealCompute.ofRat 0)) : (RealCompute.mul x y).Equiv (RealCompute.ofRat 0) := by
  have h := RealCompute.mul_equiv (x := x) (x' := x) (y := y) (y' := RealCompute.ofRat 0)
    hx hx hy zeroValid (RealCompute.equiv_refl x hx) hz
  apply RealCompute.equiv_trans (RealCompute.mul_valid hx hy)
    (RealCompute.mul_valid hx zeroValid) zeroValid h
  intro i
  apply (RealCompute.compareAt_overlap_iff _ _ i i).2
  simp [RealCompute.mul, RealCompute.mulCompute, QBox.mulRealInterval, min4, max4, minRat, maxRat2, RealCompute.ofRat, QInterval.Overlaps]

private theorem raw_add_zero {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (h₁ : x.Equiv (RealCompute.ofRat 0)) (h₂ : y.Equiv (RealCompute.ofRat 0)) :
    (RealCompute.add x y).Equiv (RealCompute.ofRat 0) := by
  apply RealCompute.equiv_trans (RealCompute.add_valid hx hy)
    (RealCompute.add_valid zeroValid zeroValid) zeroValid
    (RealCompute.add_equiv hx zeroValid hy zeroValid h₁ h₂)
  intro k
  apply (RealCompute.compareAt_overlap_iff _ _ k k).2
  change QInterval.Overlaps ((RealCompute.add (RealCompute.ofRat 0) (RealCompute.ofRat 0)).compute k)
    ((RealCompute.ofRat 0).compute k)
  simp [RealCompute.add, RealCompute.addCompute, RealCompute.ofRat, QInterval.Overlaps, Rat.zero_add]

private theorem sum_zero_equiv :
    ∀ n (f : Fin n → RealCompute), (∀ i, (f i).Valid) →
      (∀ i, (f i).Equiv (RealCompute.ofRat 0)) → (sumRaw n f).Equiv (RealCompute.ofRat 0)
  | 0, _, _, _ => RealCompute.ofRat_equiv_self 0
  | n + 1, _, hv, hz =>
    raw_add_zero (sumRaw_valid n _ (fun i => hv i.castSucc)) (hv (Fin.last n))
      (sum_zero_equiv n _ (fun i => hv i.castSucc) (fun i => hz i.castSucc)) (hz (Fin.last n))

private theorem box_zero {d : Nat} {B : RationalBox d} {f : QPoint d → RealCompute} {v : RealCompute}
    (h : HasBoxIntegral B f v) (hz : ∀ x, (f x).Equiv (RealCompute.ofRat 0)) :
    v.Equiv (RealCompute.ofRat 0) := by
  apply RawLimit.unique (RawLimit.congr_sequence h.2.1
    (v := fun _ => RealCompute.ofRat 0) (fun _ => RealCompute.ofRat_valid 0) ?_)
    (RawLimit.constant _ zeroValid)
  intro k
  let sample (code : Fin ((2 ^ k) ^ d)) :=
    f (B.dyadicCellCenter k fun i =>
      ⟨(code.val / (2 ^ k) ^ i.val) % (2 ^ k),
        Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))⟩)
  change (RealCompute.scaleRat (B.dyadicCellVolume k) (sumRaw _ sample)).Equiv (RealCompute.ofRat 0)
  have hs := RealCompute.scaleRat_equiv (r := B.dyadicCellVolume k)
    (sum_zero_equiv _ sample (fun _ => h.1 _) (fun _ => hz _))
  apply RealCompute.equiv_trans (RealCompute.scaleRat_valid (sumRaw_valid _ sample (fun _ => h.1 _)))
    (RealCompute.scaleRat_valid zeroValid) zeroValid hs
  intro i
  apply (RealCompute.compareAt_overlap_iff _ _ i i).2
  simp [RealCompute.scaleRat, RealCompute.scaleRatCompute, RealCompute.ofRat, QInterval.Overlaps]

private theorem translatedVanishes {n : Nat} {p q : QPoint (n + 1)} {r : Rat}
    {φ ψ : TestFunction (n + 1)} {alpha : MultiIndex (n + 1)}
    (hbox : ∀ x, φ.support.Contains x → close (r / 2) p x)
    (hno : ∀ z, close r p z → ¬ backwardBoundary q z)
    (hshift : ∀ x, (ψ.value x).Equiv (φ.derivative alpha (fun i => x i + q i)))
    (hr : 0 < r) : ψ.VanishesNear (OnForwardLightCone (spatialDimension := n)) := by
  refine ⟨r / 2, ?_, ?_⟩
  · simpa [Rat.div_def] using Rat.mul_pos hr (Rat.inv_pos.mpr (show (0 : Rat) < 2 by decide))
  intro c hc x hx
  refine RealCompute.equiv_trans (ψ.value_valid x) (φ.derivative_valid _ _) zeroValid
    (hshift x) (φ.derivative_vanishes_off_support _ _ ?_)
  intro inside
  have hp := hbox _ inside
  have near : close r p (fun i => c i + q i) := by
    intro i
    have h₁ := hp i
    have h₂ := hx i
    constructor <;> grind [Rat.div_def]
  apply hno _ near
  have he : (fun i => c i + q i - q i) = c := by
    funext i
    grind
  unfold backwardBoundary
  rw [he]
  exact hc

/-- Checked localization step. A test in a sufficiently small observation
box pairs to zero with the causal Duhamel solution of the perturbation. -/
theorem duhamel_vanishes_near {n : Nat} {S : TestFunctionSpace (n + 1)}
    (E : Distribution S) (hsupport : HasWavefrontSupport E)
    (hsolve : ForcedWave.SolvesForcedCauchyProblem E)
    (a b : TestFunction n) (f : TestFunction (n + 1))
    (p : QPoint (n + 1)) (r : Rat) (hr : 0 < r)
    (hdata : DataVanishNearBackwardBoundary a b f p r) :
    ∃ U : Distribution S, ∀ φ : TestFunction (n + 1),
      (∀ x, φ.support.Contains x → close (r / 2) p x) →
      (U.action φ).Equiv (RealCompute.ofRat 0) := by
  classical
  obtain ⟨U, hDuhamel, _⟩ := hsolve a b f
  refine ⟨U, ?_⟩
  intro φ hbox
  obtain ⟨T, F, B, A, hT, hF, hB, hA, hU⟩ := hDuhamel φ
  have productZero (g : RealCompute) (hg : g.Valid) (q : QPoint (n + 1))
      (ψ : TestFunction (n + 1)) (alpha : MultiIndex (n + 1))
      (hshift : ∀ y, (ψ.value y).Equiv (φ.derivative alpha (fun i => y i + q i)))
      (hsource : ∀ z, close r p z → backwardBoundary q z → g.Equiv (RealCompute.ofRat 0)) :
      (RealCompute.mul g (E.action ψ)).Equiv (RealCompute.ofRat 0) := by
    by_cases hit : ∃ z, close r p z ∧ backwardBoundary q z
    · obtain ⟨z, hclose, hboundary⟩ := hit
      have hg0 := hsource z hclose hboundary
      have h := RealCompute.mul_equiv (x := g) (x' := RealCompute.ofRat 0)
        (y := E.action ψ) (y' := E.action ψ)
        hg zeroValid (E.action_valid ψ) (E.action_valid ψ)
        hg0 (RealCompute.equiv_refl _ (E.action_valid ψ))
      apply RealCompute.equiv_trans (RealCompute.mul_valid hg (E.action_valid ψ))
        (RealCompute.mul_valid zeroValid (E.action_valid ψ)) zeroValid h
      intro k
      apply (RealCompute.compareAt_overlap_iff _ _ k k).2
      simp [RealCompute.mul, RealCompute.mulCompute, QBox.mulRealInterval, min4, max4, minRat, maxRat2, RealCompute.ofRat, QInterval.Overlaps]
    · have hzero := hsupport ψ (translatedVanishes hbox
        (fun z hz hb => hit ⟨z, hz, hb⟩) hshift hr)
      exact raw_mul_zero hg (E.action_valid ψ) hzero
  have Fzero := box_zero hF (by
    intro q
    split
    next htime =>
      exact productZero _ (f.value_valid q) q (T q) (zeroIndex _)
        (hT q (zeroIndex _)) (fun z hz hb => hdata.2 q z htime hz hb)
    next =>
      exact RealCompute.ofRat_equiv_self 0)
  have Bzero := box_zero hB (fun x =>
    productZero _ (b.value_valid x) (onTimeZero x) (T (onTimeZero x)) (zeroIndex _)
      (hT (onTimeZero x) (zeroIndex _)) (fun z hz hb => (hdata.1 x z hz hb).2))
  have Azero := box_zero hA (fun x =>
    productZero _ (a.value_valid x) (onTimeZero x)
      ((T (onTimeZero x)).coordinatePartial (timeCoordinate n))
      (incrementIndex (zeroIndex _) (timeCoordinate n))
      (hT (onTimeZero x) _) (fun z hz hb => (hdata.1 x z hz hb).1))
  have Fvalid := hF.2.1.1
  have Bvalid := hB.2.1.1
  have Avalid := hA.2.1.1
  refine RealCompute.equiv_trans (U.action_valid φ)
    (RealCompute.sub_valid (RealCompute.add_valid Fvalid Bvalid) Avalid) zeroValid
    hU ?_
  have h := RealCompute.sub_equiv (x := RealCompute.add F B) (x' := RealCompute.ofRat 0)
    (y := A) (y' := RealCompute.ofRat 0) (RealCompute.add_valid Fvalid Bvalid)
    zeroValid Avalid zeroValid
    (raw_add_zero Fvalid Bvalid Fzero Bzero) Azero
  apply RealCompute.equiv_trans (RealCompute.sub_valid (RealCompute.add_valid Fvalid Bvalid) Avalid)
    (RealCompute.sub_valid zeroValid zeroValid) zeroValid h
  intro k
  apply (RealCompute.compareAt_overlap_iff _ _ k k).2
  change QInterval.Overlaps ((RealCompute.sub (RealCompute.ofRat 0) (RealCompute.ofRat 0)).compute k)
    ((RealCompute.ofRat 0).compute k)
  simp [RealCompute.sub, RealCompute.subCompute, RealCompute.ofRat, QInterval.Overlaps, Rat.sub_self]

/-- If localized average pairings recover the ordinary value, vanishing
of those pairings gives exact vanishing of the represented point value. -/
theorem value_eq_zero_of_localized_pairings {n : Nat} {S : TestFunctionSpace (n + 1)}
    (U : Distribution S) (u : ClassicalSolution n) (p : QPoint (n + 1)) (r : Rat)
    (probe : Nat → TestFunction (n + 1))
    (hprobe : ∀ k x, (probe k).support.Contains x → close (r / 2) p x)
    (hzero : ∀ φ : TestFunction (n + 1),
      (∀ x, φ.support.Contains x → close (r / 2) p x) →
      (U.action φ).Equiv (RealCompute.ofRat 0))
    (hlimit : RawLimit.TendsTo (fun k => U.action (probe k)) (u.value p)) :
    (u.value p).Equiv (RealCompute.ofRat 0) := by
  apply RawLimit.unique (RawLimit.congr_sequence hlimit (v := fun _ => RealCompute.ofRat 0)
    (fun _ => zeroValid) (fun k => hzero (probe k) (hprobe k)))
  exact RawLimit.constant _ zeroValid

end ComputableDistributions.ClassicalHuygens


