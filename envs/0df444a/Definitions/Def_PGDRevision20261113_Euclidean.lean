-- Prove2me | Definitions.Def_PGDRevision20261113_Euclidean
-- name    : PGDRevision20261113_Euclidean
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T06:21:04.767207+00:00
-- url     : https://prove2.me/theorems/c3b80a7b-7b5e-4f9e-9b3f-c69876587cfc
-- title:
--   Fixed-penalty PGD extensions, quantitative transfer and DCA
-- statement:
--   This module reuses the existing finite-dimensional penalty and PGD interfaces. It defines actual proximal minimization, the attained-objective-minimum restriction, quadratic/Huber matching functions and the exact scaled construction for the unchanged penalty.
--   Finite-transfer quantities are computed from the actual support gap and actual executed trajectory. The DCA interface uses convex minimization equivalent to its subgradient inclusion, with the zero energy argument represented by extended-real infinity. The named extension predicates are proof targets.
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Section 2, Lemma 2.2, Proposition 2.6, Corollaries 2.7-2.8, pages 3, 6-8.

import Definitions.Def_PGDMap20261031_PGD
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open Filter Topology
open PGDMap20261031

namespace PGDRevision20261113

def ProximalPoint {d : ℕ} (r : Penalty d) (gamma : ℝ) (input output : Space d) : Prop :=
  output ∈ r.domain ∧ ∀ y ∈ r.domain,
    r.value output + ‖output - input‖ ^ 2 / (2 * gamma) ≤
      r.value y + ‖y - input‖ ^ 2 / (2 * gamma)

def PGDUpdateMap {d : ℕ} (r : Penalty d) (grad : Space d → Space d)
    (gamma : ℝ) (T : Space d → Space d) : Prop :=
  ∀ x, ProximalPoint r gamma (x - gamma • grad x) (T x)

def MappingContractionClaim : Prop :=
  ∀ (d : ℕ) (r : Penalty d) (f : Space d → ℝ) (grad T : Space d → Space d)
    (L mu gamma : ℝ), IsPenalty r → 0 ≤ mu → StrongPenalty r mu →
    0 < L → SmoothConvex f grad L → 0 < gamma → gamma * L < 2 →
    PGDUpdateMap r grad gamma T →
    (∀ x y, ‖T x - T y‖ ≤ ‖x - y‖ / (1 + gamma * mu)) ∧
    ∀ (N : ℕ) (x : ℕ → Space d), 1 ≤ N →
      (∀ i < N, x (i + 1) = T (x i)) →
      (∀ i < N - 1,
        ‖x (i + 1) - x (i + 2)‖ / gamma ≤
          (‖x i - x (i + 1)‖ / gamma) / (1 + gamma * mu)) ∧
      ∀ i < N, ‖x (N - 1) - x N‖ / gamma ≤ ‖x i - x (i + 1)‖ / gamma

def ObjectiveAttainsMinimum {d : ℕ} (r : Penalty d) (f : Space d → ℝ) : Prop :=
  ∃ x ∈ r.domain, ∀ y ∈ r.domain, totalValue r f x ≤ totalValue r f y

def attainedRatioSet {d : ℕ} (r : Penalty d) (L h : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ (f : Space d → ℝ) (grad : Space d → Space d) (x : ℕ → Space d),
    SmoothConvex f grad L ∧ IsPGDTrajectory r grad (h / L) N x ∧
    ObjectiveAttainsMinimum r f ∧ 0 < decrease r f x N ∧
    v = residualSquared (h / L) x N / (L * decrease r f x N)}

def SharpnessAttainedMinimaClaim : Prop :=
  ∀ (d : ℕ) (r : Penalty d) (L h : ℝ) (N : ℕ),
    IsPenalty r → NonSingleton r → 0 < L → validStep h → 1 ≤ N →
    IsLUB (attainedRatioSet r L h N) (curve N h (bestModulus r / L))

inductive MatchingFunction where
  | quadratic
  | huber (tau : ℝ)

def matchingValue (branch : MatchingFunction) (t : ℝ) : ℝ :=
  match branch with
  | .quadratic => t ^ 2 / 2
  | .huber tau => if |t| ≤ tau then t ^ 2 / 2 else tau * |t| - tau ^ 2 / 2

def ValidMatchingFunction (branch : MatchingFunction) : Prop :=
  match branch with
  | .quadratic => True
  | .huber tau => 0 < tau

structure TransferSetup (d : ℕ) where
  r : Penalty d
  q : ℝ
  h : ℝ
  N : ℕ
  branch : MatchingFunction
  t : ℕ → ℝ
  M : ℝ

def targetDecrease {d : ℕ} (S : TransferSetup d) : ℝ :=
  matchingValue S.branch (S.t 0) + S.q / 2 * S.t 0 ^ 2 -
    matchingValue S.branch (S.t S.N) - S.q / 2 * S.t S.N ^ 2
def targetMapping {d : ℕ} (S : TransferSetup d) : ℝ :=
  |S.t (S.N - 1) - S.t S.N| / S.h

def ValidTransferSetup {d : ℕ} (S : TransferSetup d) : Prop :=
  IsPenalty S.r ∧ NonSingleton S.r ∧ S.q = bestModulus S.r ∧
  0 ≤ S.q ∧ StrongPenalty S.r S.q ∧ validStep S.h ∧ 1 ≤ S.N ∧
  ValidMatchingFunction S.branch ∧
  (∀ i ≤ S.N, |S.t i| ≤ S.M) ∧
  (∀ i < S.N, S.t (i + 1) =
    (S.t i - S.h * deriv (matchingValue S.branch) (S.t i)) / (1 + S.h * S.q)) ∧
  0 < targetDecrease S ∧
  targetMapping S ^ 2 / targetDecrease S = curve S.N S.h S.q

structure TransferSample (d : ℕ) where
  c : Space d
  s : Space d
  v : Space d
  delta : ℝ
  x : ℕ → Space d

def residualPenalty {d : ℕ} (r : Penalty d) (q : ℝ) : Penalty d :=
  ⟨r.domain, fun x => r.value x - q / 2 * ‖x‖ ^ 2⟩

def normalizedSupportGap {d : ℕ} (S : TransferSetup d) (J : TransferSample d)
    (z : Space d) : ℝ :=
  ((residualPenalty S.r S.q).value (J.c + J.delta • z) -
    (residualPenalty S.r S.q).value J.c - J.delta * inner ℝ J.s z) / J.delta ^ 2

def supportGapValues {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : Set ℝ :=
  {v | ∃ t ∈ Set.Icc (-S.M) S.M, v = normalizedSupportGap S J (t • J.v)}

def sampleEpsilon {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : ℝ :=
  sSup (supportGapValues S J)

def liftedSmooth {d : ℕ} (S : TransferSetup d) (J : TransferSample d) (x : Space d) : ℝ :=
  J.delta ^ 2 * matchingValue S.branch (inner ℝ J.v (x - J.c) / J.delta) -
    inner ℝ (J.s + S.q • J.c) x

def liftedGradient {d : ℕ} (S : TransferSetup d) (J : TransferSample d)
    (x : Space d) : Space d :=
  (J.delta * deriv (matchingValue S.branch) (inner ℝ J.v (x - J.c) / J.delta)) • J.v -
    (J.s + S.q • J.c)

def ValidTransferSample {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : Prop :=
  Supports (residualPenalty S.r S.q) J.c J.s ∧ 0 < J.delta ∧ ‖J.v‖ = 1 ∧
  (∀ t ∈ Set.Icc (-S.M) S.M, J.c + (J.delta * t) • J.v ∈ S.r.domain) ∧
  BddAbove (supportGapValues S J) ∧
  J.x 0 = J.c + (J.delta * S.t 0) • J.v ∧
  IsPGDTrajectory S.r (liftedGradient S J) S.h S.N J.x

def sampleDecrease {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : ℝ :=
  decrease S.r (liftedSmooth S J) J.x S.N / J.delta ^ 2
def sampleMapping {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : ℝ :=
  ‖J.x (S.N - 1) - J.x S.N‖ / (S.h * J.delta)
def stateErrorRadius {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : ℝ :=
  S.N * Real.sqrt (2 * (S.h / (1 + S.h * S.q)) * sampleEpsilon S J)
def mappingErrorRadius {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : ℝ :=
  2 * stateErrorRadius S J / S.h
def decreaseErrorRadius {d : ℕ} (S : TransferSetup d) (J : TransferSample d) : ℝ :=
  (1 + S.q) * (S.M * stateErrorRadius S J + stateErrorRadius S J ^ 2 / 2) +
    sampleEpsilon S J +
    stateErrorRadius S J ^ 2 / (2 * (S.h / (1 + S.h * S.q)) * (1 + S.h * S.q) ^ 2)

def QuantitativeTransferClaim : Prop :=
  ∀ (d : ℕ) (S : TransferSetup d), ValidTransferSetup S →
    (∀ J : TransferSample d, ValidTransferSample S J →
      |sampleDecrease S J - targetDecrease S| ≤ decreaseErrorRadius S J ∧
      |sampleMapping S J - targetMapping S| ≤ mappingErrorRadius S J ∧
      (decreaseErrorRadius S J < targetDecrease S →
        0 < sampleDecrease S J ∧
        max (targetMapping S - mappingErrorRadius S J) 0 ^ 2 /
            (targetDecrease S + decreaseErrorRadius S J) ≤
          sampleMapping S J ^ 2 / sampleDecrease S J ∧
        sampleMapping S J ^ 2 / sampleDecrease S J ≤
          (targetMapping S + mappingErrorRadius S J) ^ 2 /
            (targetDecrease S - decreaseErrorRadius S J))) ∧
    ∀ J : ℕ → TransferSample d, (∀ j, ValidTransferSample S (J j)) →
      Tendsto (fun j => sampleEpsilon S (J j)) atTop (𝓝 (0 : ℝ)) →
      Asymptotics.IsBigO atTop
        (fun j => sampleMapping S (J j) ^ 2 / sampleDecrease S (J j) -
          targetMapping S ^ 2 / targetDecrease S)
        (fun j => Real.sqrt (sampleEpsilon S (J j)))

def DCATrajectory {d : ℕ} (u : Penalty d) (gradV : Space d → Space d)
    (N : ℕ) (x : ℕ → Space d) : Prop :=
  (∀ i ≤ N, x i ∈ u.domain) ∧
  ∀ i < N, ∀ y ∈ u.domain,
    u.value (x (i + 1)) - inner ℝ (gradV (x i)) (x (i + 1)) ≤
      u.value y - inner ℝ (gradV (x i)) y

def dcaEnergy (k : ℕ) (z : ℝ) : EReal :=
  if z = 0 then ⊤ else (geometricSum k z : EReal)

def DCAConvexObjectiveClaim : Prop :=
  ∀ (d : ℕ) (u : Penalty d) (v : Space d → ℝ) (gradV : Space d → Space d)
    (mu1 mu2 L2 : ℝ) (N : ℕ) (x : ℕ → Space d),
    IsPenalty u → StrongPenalty u mu1 →
    (∀ y, HasGradientAt v (gradV y) y) →
    ConvexOn ℝ Set.univ (fun y => v y - mu2 / 2 * ‖y‖ ^ 2) →
    ConvexOn ℝ Set.univ (fun y => L2 / 2 * ‖y‖ ^ 2 - v y) →
    0 < mu1 → mu2 < L2 → L2 ≤ mu1 → 0 < mu1 + mu2 → 2 ≤ N →
    DCATrajectory u gradV N x →
    mu1 / 2 * ‖x (N - 1) - x N‖ ^ 2 ≤
      ((u.value (x 0) - v (x 0)) - (u.value (x N) - v (x N))) /
        (1 + mu2 / mu1 +
          (min (dcaEnergy (N - 1) (L2 / mu1)) (dcaEnergy (N - 1) (mu2 / mu1))).toReal)

end PGDRevision20261113


