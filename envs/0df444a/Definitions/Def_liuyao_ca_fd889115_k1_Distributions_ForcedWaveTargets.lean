-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_ForcedWaveTargets
-- name    : liuyao_ca_fd889115_k1_Distributions_ForcedWaveTargets
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:39:53.98883+00:00
-- url     : https://prove2.me/theorems/a1ac6974-ed86-4bc2-88aa-9e3afa1083dc
-- title:
--   Computable analysis · ForcedWaveTargets · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/ForcedWaveTargets.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_BoxQuadrature
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_AlgebraicFunctions
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_GeometricSinCos

set_option autoImplicit true

/-! Exact targets for two independently prescribed wave kernels and their
application to the forced Cauchy problem. Coordinate zero is time. -/

open ComputableAnalysis

namespace ComputableDistributions.ForcedWave

private def point {n : Nat} (t : Rat) (x : QPoint n) : QPoint (n + 1) :=
  Fin.cases t x

private def cube (n : Nat) (r : Nat) : RationalBox n :=
  ⟨fun _ => -(r : Rat), fun _ => r, fun _ => by
    have h : 0 ≤ (r : Rat) := Rat.natCast_nonneg
    grind only⟩

private def power (q : RealCompute) : Nat → RealCompute
  | 0 => RealCompute.ofRat 1
  | k + 1 => RealCompute.mul q (power q k)

private def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

private def waveTest {n : Nat} (S : TestFunctionSpace (n + 1))
    (φ : TestFunction (n + 1)) : TestFunction (n + 1) :=
  let rec addSpatial (k : Nat) (h : k ≤ n) : TestFunction (n + 1) :=
    match k with
    | 0 => S.zero
    | k + 1 =>
      let i := spatialCoordinate (⟨k, by omega⟩ : Fin n)
      S.add (addSpatial k (by omega)) ((φ.coordinatePartial i).coordinatePartial i)
  let t := timeCoordinate n
  S.add ((φ.coordinatePartial t).coordinatePartial t)
    (S.scale (RealCompute.ofRat (-1)) (RealCompute.ofRat_valid (-1)) (addSpatial n (by omega)))

private def wavePower {n : Nat} (S : TestFunctionSpace (n + 1))
    (φ : TestFunction (n + 1)) : Nat → TestFunction (n + 1)
  | 0 => φ
  | k + 1 => waveTest S (wavePower S φ k)

private def coneShape {n : Nat} (k : Nat) (p : QPoint (n + 1)) : RealCompute :=
  let t := p (timeCoordinate n)
  let q := t ^ 2 - spatialRadiusSquared p
  if h : 0 ≤ t ∧ 0 ≤ q then
    power (sqrtRaw q (show ¬ q < 0 from Rat.not_lt.mpr h.2)) (2 * (k + 1) - (n + 1))
  else RealCompute.ofRat 0

/-- Start with the ordinary Riesz cone density at parameter 2(k+1).
Its spatial mass at time one is 1/(2k+1)!, fixing its normalization.
Apply the wave operator k times by transposition to reach parameter 2. -/
def HasRieszConstruction {n : Nat} {S : TestFunctionSpace (n + 1)}
    (E : Distribution S) : Prop :=
  ∃ (k : Nat) (normalization : RealCompute), n + 1 < 2 * (k + 1) ∧ normalization.Valid ∧
    HasBoxIntegral (cube n 1)
      (fun x => RealCompute.mul normalization (coneShape k (point 1 x)))
      (RealCompute.ofRat (1 / (factorial (2 * k + 1) : Rat))) ∧
    ∀ φ : TestFunction (n + 1),
      let ψ := wavePower S φ k
      HasBoxIntegral ψ.support
        (fun p => RealCompute.mul (RealCompute.mul normalization (coneShape k p)) (ψ.value p))
        (E.action φ)

private def frequencySquared {n : Nat} (ξ : QPoint n) : RealCompute :=
  RealCompute.scaleRat (4 * sumRat n (fun i => ξ i ^ 2)) (power GeometricTrig.pi 2)

/-- The entire multiplier sin(t√λ)/√λ, specified by finite Taylor sums.
The same formula gives t when λ = 0. -/
private def multiplierSum (t : Rat) (frequency : RealCompute) : Nat → RealCompute
  | 0 => RealCompute.ofRat 0
  | j + 1 => RealCompute.add (multiplierSum t frequency j)
      (RealCompute.scaleRat (t ^ (2 * j + 1) / (factorial (2 * j + 1) : Rat))
        (power (RealCompute.neg frequency) j))

private def cosinePhase {n : Nat} (ξ : QPoint n) (p : QPoint (n + 1)) : RealCompute :=
  GeometricTrig.sample true (2 * sumRat n (fun i => ξ i * p i.succ))

/-- The inverse spatial Fourier pairing of the even real multiplier with
a real compact spacetime test. Evenness leaves the cosine phase. Both
integrations are fixed by dyadic box integrals. -/
def HasFourierConstruction {n : Nat} {S : TestFunctionSpace (n + 1)}
    (E : Distribution S) : Prop :=
  ∃ multiplier : Rat → QPoint n → RealCompute,
    (∀ t ξ, RawLimit.TendsTo (multiplierSum t (frequencySquared ξ)) (multiplier t ξ)) ∧
    ∀ φ : TestFunction (n + 1),
      ∃ inner : QPoint n → RealCompute, ∃ stage : Nat → RealCompute,
        (∀ ξ, HasBoxIntegral φ.support (fun p =>
          if 0 ≤ p (timeCoordinate n) then
            RealCompute.mul (multiplier (p (timeCoordinate n)) ξ)
              (RealCompute.mul (cosinePhase ξ p) (φ.value p))
          else RealCompute.ofRat 0) (inner ξ)) ∧
        (∀ j, HasBoxIntegral (cube n (j + 1)) inner (stage j)) ∧
        RawLimit.TendsTo stage (E.action φ)

private def slice {n : Nat} (t : Rat) (φ : TestFunction (n + 1))
    (ψ : TestFunction n) : Prop :=
  ∀ alpha x, (ψ.derivative alpha x).Equiv
    (φ.derivative (Fin.cases 0 alpha) (point t x))

private def shifted {n : Nat} (q : QPoint (n + 1)) (φ ψ : TestFunction (n + 1)) : Prop :=
  ∀ alpha x, (ψ.derivative alpha x).Equiv (φ.derivative alpha (fun i => x i + q i))

private def pair {n : Nat} (a ψ : TestFunction n) (v : RealCompute) : Prop :=
  HasBoxIntegral a.support (fun x => RealCompute.mul (a.value x) (ψ.value x)) v

/-- Positive-time forcing and the two initial-data sources, in order:
H f, δ ⊗ b, and δ′ ⊗ a. -/
private def source {n : Nat} (a b : TestFunction n) (f φ : TestFunction (n + 1))
    (v : RealCompute) : Prop :=
  ∃ ψ ψt : TestFunction n, ∃ F B A : RealCompute,
    slice 0 φ ψ ∧ slice 0 (φ.coordinatePartial (timeCoordinate n)) ψt ∧
    HasBoxIntegral f.support (fun q =>
      if 0 ≤ q (timeCoordinate n) then RealCompute.mul (f.value q) (φ.value q)
      else RealCompute.ofRat 0) F ∧
    pair b ψ B ∧ pair a ψt A ∧
    v.Equiv (RealCompute.sub (RealCompute.add F B) A)

/-- Distributional Duhamel formula: convolve the three causal sources with
E by testing against translates of the observation test. -/
private def duhamel {n : Nat} {S : TestFunctionSpace (n + 1)} (E : Distribution S)
    (a b : TestFunction n) (f φ : TestFunction (n + 1)) (v : RealCompute) : Prop :=
  ∃ T : QPoint (n + 1) → TestFunction (n + 1), ∃ F B A : RealCompute,
    (∀ q, shifted q φ (T q)) ∧
    HasBoxIntegral f.support (fun q =>
      if 0 ≤ q (timeCoordinate n) then RealCompute.mul (f.value q) (E.action (T q))
      else RealCompute.ofRat 0) F ∧
    HasBoxIntegral b.support (fun x =>
      RealCompute.mul (b.value x) (E.action (T (point 0 x)))) B ∧
    HasBoxIntegral a.support (fun x => RealCompute.mul (a.value x)
      (E.action ((T (point 0 x)).coordinatePartial (timeCoordinate n)))) A ∧
    v.Equiv (RealCompute.sub (RealCompute.add F B) A)

private def nonnegativeTime {n : Nat} (p : QPoint (n + 1)) : Prop :=
  0 ≤ p (timeCoordinate n)

private def reachable {n : Nat} (a b : TestFunction n) (f : TestFunction (n + 1))
    (p : QPoint (n + 1)) : Prop :=
  ∃ q : QPoint (n + 1),
    ((q (timeCoordinate n) = 0 ∧
        (a.support.Contains (fun i => q i.succ) ∨ b.support.Contains (fun i => q i.succ))) ∨
      (nonnegativeTime (n := n) q ∧ f.support.Contains q)) ∧
    InForwardLightCone (spatialDimension := n) (fun i => p i - q i)

/-- The time-slice realization agrees with the causal spacetime solution;
its value and right time derivative at zero are the input data weakly. -/
private def hasTraces {n : Nat} {S : TestFunctionSpace (n + 1)} (U : Distribution S)
    (a b : TestFunction n) : Prop :=
  ∃ (X : TestFunctionSpace n) (u : Rat → Distribution X),
    (∀ ψ : TestFunction n, ∃ A B : RealCompute,
      pair a ψ A ∧ pair b ψ B ∧ ((u 0).action ψ).Equiv A ∧
      BracketDerivative.HasDerivativeAt (fun t : Rat => 0 ≤ t)
        (fun t => (u t).action ψ) (RealCompute.ofRat 0) B) ∧
    ∀ φ : TestFunction (n + 1), ∃ ψ : Rat → TestFunction n,
      (∀ t, slice t φ (ψ t)) ∧
      HasBoxIntegral (⟨fun _ : Fin 1 => φ.support.lower 0,
        fun _ => φ.support.upper 0, fun _ => φ.support.ordered 0⟩ : RationalBox 1)
        (fun q => if 0 ≤ q 0 then (u (q 0)).action (ψ (q 0)) else RealCompute.ofRat 0)
        (U.action φ)

/-- Forced weak Cauchy problem with compact smooth data, including the exact
Duhamel action, weak initial traces, causal uniqueness, and propagation. -/
def SolvesForcedCauchyProblem {n : Nat} {S : TestFunctionSpace (n + 1)}
    (E : Distribution S) : Prop :=
  ∀ (a b : TestFunction n) (f : TestFunction (n + 1)), ∃ U : Distribution S,
    (∀ φ, duhamel E a b f φ (U.action φ)) ∧
    (∀ φ, source a b f φ (waveAdjointAction U φ)) ∧
    hasTraces U a b ∧ IsSupportedIn U (reachable a b f) ∧
    ∀ V : Distribution S, IsSupportedIn V (nonnegativeTime (n := n)) →
      (∀ φ, source a b f φ (waveAdjointAction V φ)) → U.Equivalent V

/-- Construct the normalized Riesz action with its source and support laws. -/
def RieszTarget : Prop :=
  ∀ (n : Nat), 0 < n → ∀ S : TestFunctionSpace (n + 1), ∃ E : Distribution S,
    HasRieszConstruction E ∧ IsRetardedWaveFundamentalSolution E ∧
    (3 ≤ n → n % 2 = 1 → HasWavefrontSupport E)

/-- Construct the inverse Fourier pairing and prove its source and cone support. -/
def FourierTarget : Prop :=
  ∀ (n : Nat), 0 < n → ∀ S : TestFunctionSpace (n + 1), ∃ F : Distribution S,
    HasFourierConstruction F ∧ IsRetardedWaveFundamentalSolution F

/-- Identify the actions on all tests by retarded uniqueness. -/
def AgreementTarget : Prop :=
  ∀ (n : Nat), 0 < n → ∀ (S : TestFunctionSpace (n + 1)) (E F : Distribution S),
    HasRieszConstruction E → HasFourierConstruction F →
    IsRetardedWaveFundamentalSolution E → IsRetardedWaveFundamentalSolution F →
    E.Equivalent F

/-- Both constructions have the source and support laws, including strong
Huygens support, on the same test module. Their actions agree on every
test, and their common value supplies the forced Cauchy solver. -/
def AllDimensionsTarget : Prop :=
  ∀ (n : Nat), 0 < n → ∀ S : TestFunctionSpace (n + 1), ∃ E F : Distribution S,
    HasRieszConstruction E ∧ HasFourierConstruction F ∧
    IsRetardedWaveFundamentalSolution E ∧ IsRetardedWaveFundamentalSolution F ∧
    E.Equivalent F ∧ (3 ≤ n → n % 2 = 1 → HasWavefrontSupport E) ∧
    SolvesForcedCauchyProblem E

end ComputableDistributions.ForcedWave


