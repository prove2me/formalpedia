-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_TemperedFourierTargets
-- name    : liuyao_ca_fd889115_k1_Distributions_TemperedFourierTargets
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:34:40.456424+00:00
-- url     : https://prove2.me/theorems/de65e5c6-f8c5-4d28-be64-05f9177566da
-- title:
--   Computable analysis · TemperedFourierTargets · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/TemperedFourierTargets.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_BoxQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricSinCos

set_option autoImplicit true

/-! A finite-dimensional Fourier inversion milestone for tempered distributions.
Compact frequency windows use the same tagged dyadic box integral as the
compact-test transform. The limits and the two inverse identities are goals. -/

open ComputableAnalysis

namespace ComputableDistributions.TemperedFourier

open RealApproximationOrder

private def addValue (z w : ComplexActionValue) : ComplexActionValue :=
  ⟨RealCompute.add z.re w.re, RealCompute.add z.im w.im,
    RealCompute.add_valid z.re_valid w.re_valid, RealCompute.add_valid z.im_valid w.im_valid⟩

private def mulValue (z w : ComplexActionValue) : ComplexActionValue :=
  ⟨RealCompute.sub (RealCompute.mul z.re w.re) (RealCompute.mul z.im w.im),
    RealCompute.add (RealCompute.mul z.re w.im) (RealCompute.mul z.im w.re),
    RealCompute.sub_valid (RealCompute.mul_valid z.re_valid w.re_valid)
      (RealCompute.mul_valid z.im_valid w.im_valid),
    RealCompute.add_valid (RealCompute.mul_valid z.re_valid w.im_valid)
      (RealCompute.mul_valid z.im_valid w.re_valid)⟩

private def bounded (z : ComplexActionValue) (bound : Rat) : Prop :=
  Small (parameter z.re z.re_valid) bound ∧ Small (parameter z.im z.im_valid) bound

/-- The weighted supremum bounds for the mixed partials are expressed on
rational samples. The product weight gives a cofinal family of Schwartz
seminorms. -/
def SchwartzBound {d : Nat} (derivative : MultiIndex d → QPoint d → ComplexActionValue)
    (order weight : Nat) (bound : Rat) : Prop :=
  ∀ alpha, sumRawOrder alpha ≤ order → ∀ x,
    bounded (derivative alpha x)
      (bound / productRat d (fun i => (1 + qabs (x i)) ^ weight))
where
  sumRawOrder (alpha : MultiIndex d) : Nat :=
    (List.ofFn alpha).foldl (· + ·) 0

/-- A complex Schwartz test on rational coordinates. Every mixed partial
has a secant derivative witness and rapidly decreasing samples. -/
structure SchwartzTest (d : Nat) where
  derivative : MultiIndex d → QPoint d → ComplexActionValue
  partialRe : ∀ alpha i x,
    BracketDerivative.HasDerivativeAt (fun _ => True)
      (fun r => (derivative alpha (replaceCoordinate x i r)).re)
      (RealCompute.ofRat (x i)) (derivative (incrementIndex alpha i) x).re
  partialIm : ∀ alpha i x,
    BracketDerivative.HasDerivativeAt (fun _ => True)
      (fun r => (derivative alpha (replaceCoordinate x i r)).im)
      (RealCompute.ofRat (x i)) (derivative (incrementIndex alpha i) x).im
  rapidDecay : ∀ order weight, ∃ bound, 0 ≤ bound ∧ SchwartzBound derivative order weight bound

def SchwartzTest.value {d : Nat} (φ : SchwartzTest d) (x : QPoint d) : ComplexActionValue :=
  φ.derivative (zeroIndex d) x

def SchwartzTest.Equivalent {d : Nat} (φ ψ : SchwartzTest d) : Prop :=
  ∀ alpha x, (φ.derivative alpha x).Equiv (ψ.derivative alpha x)

structure SchwartzTestSpace (d : Nat) where
  add : SchwartzTest d → SchwartzTest d → SchwartzTest d
  scale : ComplexActionValue → SchwartzTest d → SchwartzTest d
  add_derivative : ∀ φ ψ alpha x,
    ((add φ ψ).derivative alpha x).Equiv
      (addValue (φ.derivative alpha x) (ψ.derivative alpha x))
  scale_derivative : ∀ z φ alpha x,
    ((scale z φ).derivative alpha x).Equiv (mulValue z (φ.derivative alpha x))

/-- A complex-linear functional with a bound by finitely many weighted
Schwartz seminorms. Its pairing respects equivalent test computations. -/
structure TemperedDistribution {d : Nat} (S : SchwartzTestSpace d) where
  action : SchwartzTest d → ComplexActionValue
  congr : ∀ φ ψ, φ.Equivalent ψ → (action φ).Equiv (action ψ)
  add : ∀ φ ψ, (action (S.add φ ψ)).Equiv (addValue (action φ) (action ψ))
  scale : ∀ z φ, (action (S.scale z φ)).Equiv (mulValue z (action φ))
  continuous : ∃ (order weight : Nat) (constant : Rat), 0 ≤ constant ∧
    ∀ (φ : SchwartzTest d) (bound : Rat), 0 ≤ bound →
      SchwartzBound φ.derivative order weight bound → bounded (action φ) (constant * bound)

def TemperedDistribution.Equivalent {d : Nat} {S : SchwartzTestSpace d}
    (T U : TemperedDistribution S) : Prop :=
  ∀ φ, (T.action φ).Equiv (U.action φ)

private def cube (d n : Nat) : RationalBox d :=
  let radius : Rat := ((n + 1 : Nat) : Rat)
  ⟨fun _ => -radius, fun _ => radius, fun _ => by
    have h : 0 ≤ radius := Rat.natCast_nonneg
    grind only⟩

private def fourierIntegrand {d : Nat} (inverse : Bool) (φ : SchwartzTest d)
    (ξ x : QPoint d) : ComplexActionValue :=
  let angle := sumRat d (fun i => (if inverse then 2 else -2) * ξ i * x i)
  let phase : ComplexActionValue :=
    ⟨GeometricTrig.sample true angle, GeometricTrig.sample false angle,
      GeometricTrig.sample_valid true angle, GeometricTrig.sample_valid false angle⟩
  mulValue (φ.value x) phase

/-- The forward or inverse test transform is specified by the actual
compact dyadic integrals and their limit in each component. -/
def IsTestTransform {d : Nat} (inverse : Bool) (φ ψ : SchwartzTest d) : Prop :=
  ∀ ξ, ∃ stage : Nat → ComplexActionValue,
    (∀ n, HasBoxIntegral (cube d n) (fun x => (fourierIntegrand inverse φ ξ x).re) (stage n).re ∧
      HasBoxIntegral (cube d n) (fun x => (fourierIntegrand inverse φ ξ x).im) (stage n).im) ∧
    RawLimit.TendsTo (fun n => (stage n).re) (ψ.value ξ).re ∧
    RawLimit.TendsTo (fun n => (stage n).im) (ψ.value ξ).im

/-- Construct the Fourier transform and its inverse on tempered
distributions in arbitrary finite dimension. The pairing is bilinear,
so transposition uses the same phase as the corresponding test transform. -/
def InversionTarget : Prop :=
  ∀ (d : Nat) (S : SchwartzTestSpace d),
    ∃ (forward inverse : SchwartzTest d → SchwartzTest d)
      (fourier undo : TemperedDistribution S → TemperedDistribution S),
      (∀ φ, IsTestTransform false φ (forward φ)) ∧
      (∀ φ, IsTestTransform true φ (inverse φ)) ∧
      (∀ T φ, ((fourier T).action φ).Equiv (T.action (forward φ))) ∧
      (∀ T φ, ((undo T).action φ).Equiv (T.action (inverse φ))) ∧
      (∀ T, (undo (fourier T)).Equivalent T ∧ (fourier (undo T)).Equivalent T)

end ComputableDistributions.TemperedFourier


