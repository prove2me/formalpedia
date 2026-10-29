-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Fluid
-- name    : BramsonQueueing_FIFOKelly_Fluid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:05:37.535995+00:00
-- url     : https://prove2.me/theorems/2713cfcc-ddde-4bf3-a7f1-e35d6cffd6de
-- title:
--   Six-component basic and FIFO fluid models
-- statement:
--   A fluid path consists of class arrival, departure, effort and queue vectors $A,D,T,Z$, and station workload and idle-time vectors $W,Y$. They satisfy the nonnegativity, cumulative monotonicity, initial-zero conventions and all six basic equations (4.50)–(4.55). Non-idling says that an increase of $Y_j$ on an interval requires a zero of $W_j$ on that interval. A model adds any specified auxiliary equations. FIFO adds
--   $$D_k(t+W_{s(k)}(t))=Z_k(0)+A_k(t).$$
--   The whole initial departure curve remains part of a solution; it is not selected from queue lengths alone. Stability means one positive $N$ such that every solution has $Z(t)=0$ whenever $t\ge N\sum_k Z_k(0)$, including zero initial queues. The additional emptying time is an extended nonnegative infimum, hence infinity if the station never empties; the maximum workload is the maximum over all stations. No stability or existence assertion is a field of these definitions.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 104–106, 111–112, 147–148; PDF 112–114, 119–120, 155–156

import Definitions.Def_BramsonQueueing_FIFOKelly_Parameters

namespace BramsonQueueing.FIFOKelly

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

/-- All six components, with no dynamics or stability bundled into the carrier. -/
structure SixPaths (K J : ℕ) where
  A : ℝ → Fin K → ℝ
  D : ℝ → Fin K → ℝ
  T : ℝ → Fin K → ℝ
  W : ℝ → Fin J → ℝ
  Y : ℝ → Fin J → ℝ
  Z : ℝ → Fin K → ℝ

def NonnegativePaths {n : ℕ} (f : ℝ → Fin n → ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ k, 0 ≤ f t k

def IncreasingPaths {n : ℕ} (f : ℝ → Fin n → ℝ) : Prop :=
  ∀ k, MonotoneOn (fun t => f t k) (Ici 0)

/-- Non-idling in the exact interval formulation on printed page 103. -/
def Nonidling {J : ℕ} (W Y : ℝ → Fin J → ℝ) : Prop :=
  ∀ j a b, 0 ≤ a → a ≤ b → Y a j < Y b j →
    ∃ t ∈ Icc a b, W t j = 0

/-- Basic fluid equations (4.50)--(4.56), before any discipline is imposed. -/
def BasicFluid {K J : ℕ} (p : Parameters K J) (X : SixPaths K J) : Prop :=
  NonnegativePaths X.A ∧ NonnegativePaths X.D ∧ NonnegativePaths X.T ∧
  NonnegativePaths X.W ∧ NonnegativePaths X.Y ∧ NonnegativePaths X.Z ∧
  IncreasingPaths X.A ∧ IncreasingPaths X.D ∧ IncreasingPaths X.T ∧
  IncreasingPaths X.Y ∧
  X.A 0 = 0 ∧ X.D 0 = 0 ∧ X.T 0 = 0 ∧ X.Y 0 = 0 ∧
  (∀ t, 0 ≤ t → ∀ k,
    X.A t k = p.data.lam k * t + ∑ l, p.data.P l k * X.D t l) ∧
  (∀ t, 0 ≤ t → ∀ k, X.Z t k = X.Z 0 k + X.A t k - X.D t k) ∧
  (∀ t, 0 ≤ t → ∀ j,
    X.W t j = ∑ k, if p.data.p k = j then
      p.data.m k * (X.Z 0 k + X.A t k) - X.T t k else 0) ∧
  (∀ t, 0 ≤ t → ∀ j,
    (∑ k, if p.data.p k = j then X.T t k else 0) + X.Y t j = t) ∧
  Nonidling X.W X.Y ∧
  (∀ t, 0 ≤ t → ∀ k, X.T t k = p.data.m k * X.D t k)

/-- A model can impose additional equations; the basic equations always remain. -/
structure FluidModel (K J : ℕ) where
  parameters : Parameters K J
  auxiliary : SixPaths K J → Prop

def FluidModel.Solution {K J : ℕ} (M : FluidModel K J) (X : SixPaths K J) : Prop :=
  BasicFluid M.parameters X ∧ M.auxiliary X

def FluidStable {K J : ℕ} (solutions : SixPaths K J → Prop) : Prop :=
  ∃ N : ℝ, 0 < N ∧ ∀ X, solutions X →
    ∀ t, 0 ≤ t → N * (∑ k, X.Z 0 k) ≤ t → X.Z t = 0

def basicModel {K J : ℕ} (p : Parameters K J) : FluidModel K J :=
  ⟨p, fun _ => True⟩

/-- FIFO equation (5.18). The unrestricted initial part of D is the initial
departure curve (5.19); initial queue lengths alone do not fix it. -/
def FIFO {K J : ℕ} (p : Parameters K J) (X : SixPaths K J) : Prop :=
  ∀ t, 0 ≤ t → ∀ k,
    X.D (t + X.W t (p.data.p k)) k = X.Z 0 k + X.A t k

def fifoModel {K J : ℕ} (p : Parameters K J) : FluidModel K J :=
  ⟨p, FIFO p⟩

noncomputable def maximumWorkload {K J : ℕ} (X : SixPaths K J) (t : ℝ) : ℝ :=
  max 0 (⨆ j, X.W t j)

/-- Extended nonnegative time: a station that never empties has time infinity. -/
noncomputable def emptyingTime {K J : ℕ} (X : SixPaths K J) (j : Fin J)
    (t : ℝ) : ℝ≥0∞ :=
  ⨅ (r : ℝ≥0) (_ : X.W (t + r) j = 0), (r : ℝ≥0∞)

end BramsonQueueing.FIFOKelly


