-- Prove2me | Definitions.Def_MaxPressure_Throughput_Dynamics
-- name    : MaxPressure_Throughput_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:47:35.831086+00:00
-- url     : https://prove2.me/theorems/c6efbae0-a64f-4914-b264-05a28970e7ca
-- title:
--   Stochastic primitives, network equations and maximum-pressure process (3)–(8), (38)–(55)
-- statement:
--   For each activity $j$, the primitive processing times $\eta_j(\ell)$ and cumulative routing counts $\Phi^j_{ii'}(\ell)$ describe completions and destination buffers. Their almost-sure long-run limits are $m_j$ and $P^j_{ii'}$ in (3)–(4). The completion count $S_j(t)$ is the largest number of jobs whose total required processing time is at most $t$. The buffer path $Z$ and cumulative activity-time path $T$ satisfy the network flow and capacity equations (39)–(43).
--
--   A preemptive, processor-splitting maximum-pressure process records the cumulative time $T^a$ spent on each extreme allocation $a$. Its activity time obeys $T_j(t)=\sum_{a\in\mathcal E}a_jT^a(t)$ and $\sum_aT^a(t)=t$. If another extreme allocation is feasible by the buffer threshold $J$ and has strictly larger pressure throughout an interval, $T^a$ cannot increase there. This is the pathwise policy consequence used in the proof of Lemma 5. A fluid limit is a uniform-on-compact limit of the paths scaled by positive factors tending to infinity.
--
--   These definitions connect stochastic paths to the deterministic fluid model and the pathwise stability target.
--
--   **Formalization Note** Routing rows sum to the number of processed jobs only when the activity processes that buffer, correcting a contradiction on p. 199. Completion counts lie in $\mathbb N\cup\{\infty\}$; the network equations require them finite before converting to natural numbers. The compact-time distance uses the $\ell^1$ norm from the referenced Bell–Williams Paths definition.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), pp. 199–201, 212–214, §§2–3, A.1–A.3, (3)–(4), (8), (38)–(55), Definition 6; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Network
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory Filter Topology

namespace MaxPressure.Throughput

/-- Processing times and cumulative routing counts of §§2.2, 2.5. -/
structure Primitives (I J : ℕ) (Ω : Type*) where
  eta : Fin J → ℕ → Ω → ℝ
  Phi : Fin J → Fin (I + 1) → Fin (I + 1) → ℕ → Ω → ℕ

/-- The sample-path laws of large numbers (3) and (4). -/
def Primitives.GoodSample {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (P : Primitives I J Ω) (ω : Ω) : Prop :=
  (∀ j, Tendsto (fun n : ℕ =>
      BellWilliams2001.ThresholdPolicy.partialSum (fun l => P.eta j l ω) n / n)
      atTop (𝓝 (N.m j))) ∧
  (∀ j i i', Tendsto (fun l : ℕ => (P.Phi j i i' l ω : ℝ) / l)
      atTop (𝓝 (N.P j i i')))

/-- Conditions on the primitives, including (3)–(4). The routing row sum is
restricted to buffers processed by the activity, correcting the contradiction
between the two adjacent sentences on p. 199. -/
def Primitives.Valid {I J K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (N : Network I J K) (P : Primitives I J Ω) (Pr : Measure Ω) : Prop :=
  (∀ j l ω, 0 ≤ P.eta j l ω) ∧
  (∀ j l, Measurable (P.eta j l)) ∧
  (∀ j i i' l, Measurable (P.Phi j i i' l)) ∧
  (∀ j i i' l ω, 1 ≤ l → N.B j i = 0 → P.Phi j i i' l ω = 0) ∧
  (∀ j l ω, 1 ≤ l → P.Phi j 0 0 l ω = 0) ∧
  (∀ j i l ω, 1 ≤ l → N.B j i = 1 →
    ∑ i', P.Phi j i i' l ω = l) ∧
  (∀ j i i' ω, P.Phi j i i' 0 ω = 0) ∧
  (∀ j i i' l l' ω, l ≤ l' → P.Phi j i i' l ω ≤ P.Phi j i i' l' ω) ∧
  ∀ᵐ ω ∂Pr, P.GoodSample N ω

/-- Completion count (38), with value in ℕ∞ so infinitely many completions
are represented by ⊤. -/
noncomputable def completions {I J : ℕ} {Ω : Type*}
    (P : Primitives I J Ω) (j : Fin J) (ω : Ω) (t : ℝ) : ℕ∞ :=
  BellWilliams2001.ThresholdPolicy.renewalCount
    (BellWilliams2001.ThresholdPolicy.partialSum (fun l => P.eta j l ω)) t

/-- Stochastic network equations (39)–(43) along a sample path. Finiteness of
the completion count blocks `.toNat` from mapping ⊤ to 0. -/
def NetworkEquations {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (P : Primitives I J Ω)
    (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω) : Prop :=
  (∀ t, 0 ≤ t → ∀ j, completions P j ω (T ω t j) ≠ ⊤) ∧
  (∀ t, 0 ≤ t → ∀ i,
    Z ω t i = Z ω 0 i +
      ∑ i' : Fin (I + 1), ∑ j : Fin J,
        (P.Phi j i' i.succ
          ((completions P j ω (T ω t j)).toNat *
            (if N.B j i' = 1 then 1 else 0)) ω : ℝ) -
      ∑ j : Fin J,
        (completions P j ω (T ω t j)).toNat * N.B j i.succ) ∧
  (∀ t, 0 ≤ t → ∀ i, 0 ≤ Z ω t i) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k, N.inputProc k →
    ∑ j, N.A k j * (T ω t j - T ω s j) = t - s) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k,
    ∑ j, N.A k j * (T ω t j - T ω s j) ≤ t - s) ∧
  MonotoneOn (T ω) (Set.Ici (0 : ℝ)) ∧ T ω 0 = 0

/-- The activity time T of (49), computed from the times spent at extreme
allocations. -/
def activityTime {J : ℕ} {Ω : Type*} (E : Finset (Fin J → ℝ))
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω) (t : ℝ) (j : Fin J) : ℝ :=
  ∑ a ∈ E, a j * Ta ω a t

/-- The pathwise consequence of Definition 1 used in (56)–(58), together with
(49)–(51). Whenever a feasible extreme allocation strictly dominates a
throughout an interval, no time is assigned to a on that interval. -/
noncomputable def MPProcess {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (E : Finset (Fin J → ℝ))
    (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω) : Prop :=
  (∀ a ∈ E, MonotoneOn (Ta ω a) (Set.Ici (0 : ℝ)) ∧ Ta ω a 0 = 0) ∧
  (∀ t, 0 ≤ t → ∑ a ∈ E, Ta ω a t = t) ∧
  (∀ a ∈ E, ∀ s t, 0 ≤ s → s ≤ t →
    (∀ tau ∈ Set.Icc s t, ∃ a' ∈ E,
      (∀ i ∈ constituentBuffers N a', (J : ℝ) ≤ Z ω tau i) ∧
      pressure N a (Z ω tau) < pressure N a' (Z ω tau)) →
    Ta ω a t = Ta ω a s)

/-- Pathwise stability (8), with the almost-sure quantifier outside all
buffers. -/
def PathwiseStable {I : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) (Z : Ω → ℝ → Fin I → ℝ) : Prop :=
  ∀ᵐ ω ∂Pr, ∀ i, Tendsto (fun t : ℝ => Z ω t i / t) atTop (𝓝 0)

/-- Definition 6: fluid scaling along a positive real sequence tending to
infinity, and uniform convergence on compact time intervals. -/
noncomputable def IsFluidLimit {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (P : Primitives I J Ω)
    (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ)
    (ω : Ω) (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  P.GoodSample N ω ∧
  ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop atTop ∧
    (∀ t, 0 ≤ t →
      Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist
        (fun s i => (r n)⁻¹ * Z ω (r n * s) i) Zb t) atTop (𝓝 0)) ∧
    (∀ t, 0 ≤ t →
      Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist
        (fun s j => (r n)⁻¹ * T ω (r n * s) j) Tb t) atTop (𝓝 0))

/-- Extended fluid limit retaining the cumulative allocation times used in
Lemma 5. All components converge along the same scaling sequence. -/
noncomputable def IsMPFluidLimit {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (P : Primitives I J Ω)
    (E : Finset (Fin J → ℝ)) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (Tab : (Fin J → ℝ) → ℝ → ℝ) : Prop :=
  P.GoodSample N ω ∧
  ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop atTop ∧
    (∀ t, 0 ≤ t → Tendsto (fun n =>
      BellWilliams2001.ThresholdPolicy.supDist
        (fun s i => (r n)⁻¹ * Z ω (r n * s) i) Zb t) atTop (𝓝 0)) ∧
    (∀ t, 0 ≤ t → Tendsto (fun n =>
      BellWilliams2001.ThresholdPolicy.supDist
        (fun s j => (r n)⁻¹ * activityTime E Ta ω (r n * s) j) Tb t)
      atTop (𝓝 0)) ∧
    (∀ a ∈ E, ∀ t, 0 ≤ t → Tendsto (fun n =>
      BellWilliams2001.ThresholdPolicy.supDist
        (fun s (_ : Fin 1) => (r n)⁻¹ * Ta ω a (r n * s))
        (fun s (_ : Fin 1) => Tab a s) t) atTop (𝓝 0))

end MaxPressure.Throughput


