-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_HeatDuhamelTargets
-- name    : liuyao_ca_fd889115_k1_Distributions_HeatDuhamelTargets
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:34:03.943132+00:00
-- url     : https://prove2.me/theorems/1f954be8-aa96-4b26-8e87-d84157cc7e82
-- title:
--   Computable analysis · HeatDuhamelTargets · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/HeatDuhamelTargets.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_BoxQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricSinCos
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-! A companion target for Duhamel's principle for the heat equation.
All pairings and convolutions are specified by dyadic box integrals. -/

open ComputableAnalysis

namespace ComputableDistributions.HeatDuhamel

private def power (q : RealCompute) : Nat → RealCompute
  | 0 => RealCompute.ofRat 1
  | k + 1 => RealCompute.mul q (power q k)

private def point {n : Nat} (t : Rat) (x : QPoint n) : QPoint (n + 1) :=
  Fin.cases t x

private def timeBox (a b : Rat) (h : a ≤ b) : RationalBox 1 :=
  ⟨fun _ => a, fun _ => b, fun _ => h⟩

private def spatialBox {n : Nat} (B : RationalBox (n + 1)) : RationalBox n :=
  ⟨fun i => B.lower i.succ, fun i => B.upper i.succ, fun i => B.ordered i.succ⟩

private def wholeSpaceIntegral {n : Nat} (f : QPoint n → RealCompute) (value : RealCompute) : Prop :=
  ∃ stage : Nat → RealCompute,
    (∀ k, let r : Rat := ((k + 1 : Nat) : Rat)
          let B : RationalBox n := ⟨fun _ => -r, fun _ => r, fun _ => by
            have h : 0 ≤ r := Rat.natCast_nonneg
            grind only⟩
          HasBoxIntegral B f (stage k)) ∧
    RawLimit.TendsTo stage value

/-- The Gaussian density with the spatial factor pi to the negative half
dimension cleared. Normalized identities below restore that factor. -/
private def gaussian {n : Nat} (t : Rat) (ht : 0 < t) (x : QPoint n) : RealCompute :=
  let q := 4 * t
  have hq : 0 < q := Rat.mul_pos (by decide) ht
  let invRoot := sqrtRaw q⁻¹ (Rat.not_lt.mpr (Rat.le_of_lt (Rat.inv_pos.mpr hq)))
  let exponent := -(sumRat n (fun i => x i ^ 2)) / q
  RealCompute.mul (power invRoot n) { compute := RealSeries.expCompute exponent }

private def gaussianAt {n : Nat} (t : Rat) (x : QPoint n) : RealCompute :=
  if ht : 0 < t then gaussian t ht x else RealCompute.ofRat 0

private def positivePart {n : Nat} (f : QPoint (n + 1) → RealCompute)
    (q : QPoint (n + 1)) : RealCompute :=
  if 0 ≤ q (timeCoordinate n) then f q else RealCompute.ofRat 0

/-- Convolution law for the heat semigroup, with its normalization cleared. -/
def HasSemigroupLaw (n : Nat) (normalization : RealCompute) : Prop :=
  ∀ (s t : Rat), 0 < s → 0 < t → ∀ (x : QPoint n),
    wholeSpaceIntegral (fun y =>
      RealCompute.mul (gaussianAt s (fun i => x i - y i)) (gaussianAt t y))
      (RealCompute.mul normalization (gaussianAt (s + t) x))

/-- Causal spacetime action of the time slices, and its weak heat equation
with the source due to the initial data. -/
private def hasWeakEquation {n : Nat} (a : TestFunction n) (f : TestFunction (n + 1))
    (u : Rat → QPoint n → RealCompute) : Prop :=
  ∀ φ : TestFunction (n + 1), ∃ U F A : RealCompute,
    HasBoxIntegral φ.support (positivePart (n := n) (fun p =>
      let t := p (timeCoordinate n)
      let x := fun i : Fin n => p i.succ
      let timePartial := (φ.coordinatePartial (timeCoordinate n)).value p
      let laplacian := sumRaw n (fun i =>
        ((φ.coordinatePartial (spatialCoordinate i)).coordinatePartial (spatialCoordinate i)).value p)
      RealCompute.mul (u t x) (RealCompute.neg (RealCompute.add timePartial laplacian)))) U ∧
    HasBoxIntegral f.support (positivePart (n := n) (fun p =>
      RealCompute.mul (f.value p) (φ.value p))) F ∧
    HasBoxIntegral a.support (fun x => RealCompute.mul (a.value x) (φ.value (point 0 x))) A ∧
    U.Equiv (RealCompute.add F A)

/-- The forced heat formula on compact smooth data. For the time integral
use dyadic boxes on the bounded time interval, cutting off the singular
endpoint before taking the limit. -/
def SolvesForcedHeat {n : Nat} (normalization : RealCompute)
    (a : TestFunction n) (f : TestFunction (n + 1)) (u : Rat → QPoint n → RealCompute) : Prop :=
  (∀ t, 0 ≤ t → ∀ x, (u t x).Valid) ∧
  (∀ x, (u 0 x).Equiv (a.value x)) ∧
  (∀ x m (ε : QPos), ∃ δ : Rat, 0 < δ ∧ ∀ t : Rat, 0 < t → t ≤ δ →
    RawLimit.InInterval (u t x) (QInterval.expand ((a.value x).compute m) ε.val)) ∧
  hasWeakEquation a f u ∧
  ∀ t : Rat, ∀ ht : 0 < t, ∀ x : QPoint n, ∃ I : RealCompute,
    ∃ (F : Rat → RealCompute) (stage : Nat → RealCompute) (J : RealCompute),
      HasBoxIntegral a.support (fun y =>
        RealCompute.mul (gaussianAt t (fun i => x i - y i)) (a.value y)) I ∧
      (∀ s, 0 ≤ s → s < t →
        HasBoxIntegral (spatialBox f.support) (fun y =>
          RealCompute.mul (gaussianAt (t - s) (fun i => x i - y i)) (f.value (point s y))) (F s)) ∧
      (∀ k, HasBoxIntegral (timeBox 0 t (Rat.le_of_lt ht)) (fun q =>
        if 0 ≤ q 0 ∧ q 0 < t ∧ RawLimit.allowance k ≤ t - q 0 then F (q 0)
        else RealCompute.ofRat 0) (stage k)) ∧
      RawLimit.TendsTo stage J ∧
      (RealCompute.mul normalization (u t x)).Equiv (RealCompute.add I J)

/-- Construct the normalized Gaussian semigroup in each positive spatial
dimension and derive the forced formula with its weak equation and trace. -/
def CompanionTarget : Prop :=
  ∃ rootPi : RealCompute, rootPi.Valid ∧ rootPi.Pos ∧
    (RealCompute.mul rootPi rootPi).Equiv GeometricTrig.pi ∧
    ∀ n : Nat, 0 < n →
      let normalization := power rootPi n
      (∀ t : Rat, 0 < t → wholeSpaceIntegral (gaussianAt (n := n) t) normalization) ∧
      HasSemigroupLaw n normalization ∧
      ∀ (a : TestFunction n) (f : TestFunction (n + 1)), ∃ u,
        SolvesForcedHeat normalization a f u

end ComputableDistributions.HeatDuhamel


