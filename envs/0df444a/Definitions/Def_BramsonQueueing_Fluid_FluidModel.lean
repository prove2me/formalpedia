-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_FluidModel
-- name    : BramsonQueueing_Fluid_FluidModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:54.803135+00:00
-- url     : https://prove2.me/theorems/d3fd8ddd-1411-47c3-921a-b80d0e0a1dd8
-- title:
--   Six-component basic fluid equations and uniform draining stability
-- statement:
--   A fluid path consists of cumulative arrivals $A$, departures $D$, service effort $T$, immediate workload $W$, cumulative idle time $Y$, and queue mass $Z$, all indexed by nonnegative real time. All components are nonnegative; $A,D,T,Y$ are nondecreasing. For network data $(\alpha,m,P)$, with constituency matrix $C$ and diagonal mean-service matrix $M$, the basic equations are
--   $$A(t)=\alpha t+P^\mathsf{T}D(t),\quad Z(t)=Z(0)+A(t)-D(t),$$
--   $$W(t)=CM(Z(0)+A(t))-CT(t),\quad CT(t)+Y(t)=et,\quad T(t)=MD(t).$$
--   Nonidling says that whenever $Y_j$ increases over an interval, $W_j$ vanishes at some point of that interval. Zero initial cumulative values and Lipschitz continuity follow from these equations. A fluid model adds a predicate of auxiliary discipline equations. Stability means one $N>0$ works for every solution:
--   $$Z(t)=0\quad\text{for every }t\ge N|Z(0)|.$$
--   This includes zero initial mass and all subsequent times. No uniqueness is imposed. The module also defines simultaneous uniform-on-compact convergence and scaling of all six components.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Section 4.3, printed 102–106 / PDF 110–114, equations (4.40), (4.50)–(4.61).

import Definitions.Def_BramsonQueueing_Fluid_NetworkData

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- The six components in (4.40), on nonnegative real time. -/
structure SixPath (K J : ℕ) where
  A : ℝ≥0 → Fin K → ℝ
  D : ℝ≥0 → Fin K → ℝ
  T : ℝ≥0 → Fin K → ℝ
  W : ℝ≥0 → Fin J → ℝ
  Y : ℝ≥0 → Fin J → ℝ
  Z : ℝ≥0 → Fin K → ℝ

/-- Nonnegativity and monotonicity required in §4.3. -/
def FluidRegular {K J : ℕ} (q : SixPath K J) : Prop :=
  (∀ t k, 0 ≤ q.A t k ∧ 0 ≤ q.D t k ∧ 0 ≤ q.T t k ∧ 0 ≤ q.Z t k) ∧
  (∀ t j, 0 ≤ q.W t j ∧ 0 ≤ q.Y t j) ∧
  (∀ k, Monotone (fun t => q.A t k) ∧ Monotone (fun t => q.D t k) ∧
    Monotone (fun t => q.T t k)) ∧
  (∀ j, Monotone (fun t => q.Y t j))

/-- The basic fluid equations (4.50)–(4.55). The support formulation of
nonidling is the source's definition of "can only increase when W = 0".
Continuity follows from the equations; it is not an additional hypothesis. -/
def BasicFluid {K J : ℕ} (d : NetworkData K J) (q : SixPath K J) : Prop :=
  FluidRegular q ∧
  (∀ t k, q.A t k = d.alpha k * t + ∑ l, d.routing l k * q.D t l) ∧
  (∀ t k, q.Z t k = q.Z 0 k + q.A t k - q.D t k) ∧
  (∀ t j, q.W t j =
    (∑ k ∈ Finset.univ.filter (fun k => d.station k = j),
      d.meanService k * (q.Z 0 k + q.A t k)) -
    ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), q.T t k) ∧
  (∀ t j, (∑ k ∈ Finset.univ.filter (fun k => d.station k = j), q.T t k) +
    q.Y t j = t) ∧
  (∀ j s t, s ≤ t → q.Y s j < q.Y t j →
    ∃ u ∈ Set.Icc s t, q.W u j = 0) ∧
  (∀ t k, q.T t k = d.meanService k * q.D t k)

/-- A model adds any discipline equations to the basic equations. -/
structure FluidModel {K J : ℕ} (d : NetworkData K J) where
  auxiliary : SixPath K J → Prop

def FluidModel.Solution {K J : ℕ} {d : NetworkData K J}
    (model : FluidModel d) (q : SixPath K J) : Prop :=
  BasicFluid d q ∧ model.auxiliary q

def basicModel {K J : ℕ} (d : NetworkData K J) : FluidModel d := ⟨fun _ => True⟩

/-- One draining coefficient, uniform over all solutions, including zero initial mass. -/
def StableFamily {K J : ℕ} (F : SixPath K J → Prop) : Prop :=
  ∃ N : ℝ, 0 < N ∧ ∀ q, F q → ∀ t : ℝ≥0,
    N * mass (q.Z 0) ≤ t → q.Z t = 0

def FluidModel.Stable {K J : ℕ} {d : NetworkData K J} (model : FluidModel d) : Prop :=
  StableFamily model.Solution

/-- Uniform convergence on every compact time interval of all six components. -/
def SixUOC {K J : ℕ} (f : ℕ → SixPath K J) (q : SixPath K J) : Prop :=
  ∀ H : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ≤ H,
    (∀ k, |(f n).A t k - q.A t k| < ε ∧ |(f n).D t k - q.D t k| < ε ∧
      |(f n).T t k - q.T t k| < ε ∧ |(f n).Z t k - q.Z t k| < ε) ∧
    (∀ j, |(f n).W t j - q.W t j| < ε ∧ |(f n).Y t j - q.Y t j| < ε)

noncomputable def scaleSix {K J : ℕ} (a : ℝ≥0) (q : SixPath K J) : SixPath K J where
  A t k := q.A (a * t) k / a
  D t k := q.D (a * t) k / a
  T t k := q.T (a * t) k / a
  W t j := q.W (a * t) j / a
  Y t j := q.Y (a * t) j / a
  Z t k := q.Z (a * t) k / a

end BramsonQueueing.Fluid


