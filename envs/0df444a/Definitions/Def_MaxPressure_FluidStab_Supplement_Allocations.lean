-- Prove2me | Definitions.Def_MaxPressure_FluidStab_Supplement_Allocations
-- name    : MaxPressure_FluidStab_Supplement_Allocations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:02:34.2733+00:00
-- url     : https://prove2.me/theorems/59ce13b9-b30b-446d-9ffc-d98c7afd6800
-- title:
--   §7, p. 206 — integer allocations, SAP, integer EAA and physical decision states
-- statement:
--   Let $N$ be the published network data. The integer allocation set $\mathcal N$ contains every nonnegative integer allocation satisfying (1)–(2), including service idling. Its definition is reused through a field-preserving conversion to the published reversed-Leontief network type; no reversed-Leontief property is assumed. A finite enumeration $F$ must contain exactly $\mathcal N$. SAP feasibility means
--
--   $$\exists\pi\ge0,\quad \sum_{a\in F}\pi_a=1,\qquad R\left(\sum_{a\in F}a\pi_a\right)=0.$$
--
--   Integer EAA replaces $\mathcal E$ by $\mathcal N$ in Assumption 1 and uses an attained maximizer. Integer occupation clocks use the published activity-time sum. Equation (28) uses an attained greatest pressure at regular positive times.
--
--   A decision snapshot consists of buffer contents and the unfinished activities. Its physical invariants assert nonnegative contents, compatible unfinished processor commitments and enough jobs for all held constituencies. Physical feasibility reserves held jobs, supplies distinct fresh jobs for new activities, and in the nonpreemptive case preserves every unfinished activity at level one. Feasible extremes are the intersection of this physical set with the published extreme points.
--
--   These interfaces are shared by the necessity, sufficiency and nonpreemption results. The local snapshot invariants do not assert existence of a feasible extreme allocation.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), §7, p. 206 — integer allocations, SAP, integer EAA and physical decision states

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network
import Definitions.Def_MaxPressure_Throughput_Dynamics
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology Matrix

variable {I J K : ℕ}

/-- Field-preserving transport between the published copies of the same §2 data. -/
def throughputNetwork (N : FluidStab.Network I J K) : Throughput.Network I J K :=
  ⟨N.A, N.B, N.inputProc, N.m, N.P⟩

def reversedNetwork (N : FluidStab.Network I J K) : ReversedLeontief.Network I J K :=
  ⟨N.A, N.B, N.inputProc, N.m, N.P⟩

/-- All integer allocations, including service idling, using the published definition. -/
def integerAllocs (N : FluidStab.Network I J K) : Set (Fin J → ℝ) :=
  ReversedLeontief.intAllocs (reversedNetwork N)

/-- A finite enumeration is only an interface for finite sums; it contains every integer allocation. -/
def EnumeratesInteger (N : FluidStab.Network I J K) (F : Finset (Fin J → ℝ)) : Prop :=
  (F : Set (Fin J → ℝ)) = integerAllocs N

/-- SAP (24)–(27): x is computed from π, rather than freely supplied. -/
def SAPFeasible (N : FluidStab.Network I J K) : Prop :=
  ∃ (F : Finset (Fin J → ℝ)) (π : (Fin J → ℝ) → ℝ),
    EnumeratesInteger N F ∧ (∀ a ∈ F, 0 ≤ π a) ∧ (∑ a ∈ F, π a) = 1 ∧
    R N *ᵥ (fun j => ∑ a ∈ F, a j * π a) = 0

/-- Assumption 1 with 𝒩 in place of ℰ. -/
def IntegerEAA (N : FluidStab.Network I J K) : Prop :=
  ∀ z : Fin I → ℝ, (∀ i, 0 ≤ z i) →
    ∃ a ∈ integerAllocs N, (∀ b ∈ integerAllocs N, pressure N b z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i

/-- Occupation clocks (49)–(51), with 𝒩 replacing ℰ. -/
def IntegerClocks (N : FluidStab.Network I J K) (F : Finset (Fin J → ℝ))
    (Ta : (Fin J → ℝ) → ℝ → ℝ) (T : ℝ → Fin J → ℝ) : Prop :=
  EnumeratesInteger N F ∧
  (∀ a ∈ F, MonotoneOn (Ta a) (Set.Ici 0) ∧ Ta a 0 = 0) ∧
  (∀ t, 0 ≤ t → ∑ a ∈ F, Ta a t = t) ∧
  ∀ t, 0 ≤ t → ∀ j, T t j = Throughput.activityTime F (fun (_ : Unit) => Ta) () t j

/-- Equation (28), including attainment and only at regular positive times. -/
noncomputable def IntegerFluidEq (N : FluidStab.Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  ∀ t, IsRegular Zb Tb t →
    IsGreatest ((fun a => pressure N a (Zb t)) '' integerAllocs N)
      (pressure N (deriv Tb t) (Zb t))

/-- A physical decision state: the unfinished activities retain their constituent jobs.
The jobs remain in Z until completion, as on pp. 200 and 212. -/
structure Snapshot (I J : ℕ) where
  z : Fin I → ℝ
  unfinished : Finset (Fin J)

/-- Physical invariants, not existence of a feasible extreme allocation. Input processors
may be temporarily free at a completion decision and will have to be refilled. -/
def Snapshot.Legal (N : FluidStab.Network I J K) (s : Snapshot I J) : Prop :=
  (∀ i, 0 ≤ s.z i) ∧
  (∀ k, (∑ j ∈ s.unfinished, N.A k j) ≤ 1) ∧
  ∀ i, (∑ j ∈ s.unfinished, N.B j i.succ) ≤ s.z i

/-- Fresh-job feasibility: all unfinished activities retain their jobs, including frozen
ones; each newly started activity needs a distinct fresh HOL job in every constituency.
`np` additionally retains all unfinished processor commitments at level one. -/
noncomputable def physicallyFeasible (N : FluidStab.Network I J K) (s : Snapshot I J)
    (np : Bool) : Set (Fin J → ℝ) :=
  {a | a ∈ allocSet N ∧
    (np = true → ∀ j ∈ s.unfinished, a j = 1) ∧
    ∀ i, (∑ j : Fin J, if 0 < a j ∧ j ∉ s.unfinished then N.B j i.succ else 0) ≤
      s.z i - ∑ j ∈ s.unfinished, N.B j i.succ}

/-- The same ℰ(t) is used in Lemma 2 and the policy of Theorem 9. -/
noncomputable def feasibleExtremes (N : FluidStab.Network I J K) (s : Snapshot I J) :=
  extremeAllocs N ∩ physicallyFeasible N s true

end MaxPressure.FluidStab.Supplement


