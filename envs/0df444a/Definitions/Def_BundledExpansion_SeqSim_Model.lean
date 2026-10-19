-- Prove2me | Definitions.Def_BundledExpansion_SeqSim_Model
-- name    : BundledExpansion_SeqSim_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:27.221989+00:00
-- url     : https://prove2.me/theorems/8de7ad6e-dfd8-4d43-95a1-d6859f6c2490
-- title:
--   §3 — two-attribute bundled capacity expansion model
-- statement:
--   A provider must meet deterministic demand for two capacity attributes over $[0,T]$ using two fixed-ratio cluster types. One unit of cluster type $j$ supplies $a_{ij}$ units of attribute $i$. The demand rate is $d_i(t)$, cumulative demand is $D_i(s,t)=\int_s^t d_i(u)\,du$, the purchase price is $c_j$, the holding rate is $h_i$, and each expansion incurs fixed cost $A$. A sequential cycle buys its leading cluster $m\ge1$ times and then the other cluster once; a simultaneous cycle buys both types at each expansion.
--
--   $$
--   \operatorname{cost}=\operatorname{fixed}+\sum_j c_j Q_j+\sum_i h_i\int_0^T E_i(t)\,dt,
--   $$
--
--   where $E_i(t)$ is supplied capacity minus cumulative demand, including any expansion at time $t$. Admissible cycles have strictly increasing times, no shortage, balanced capacities at cycle boundaries, and the paper’s Assumption 1 on sequential leading intervals. The optimal sequential and simultaneous costs are the infima over all such policies; the simultaneous fixed cost is $\beta A$ per joint expansion.
--
--   This model keeps the actual capacity trajectory and its integral available for the cost identities and threshold theorem. The determinant $\alpha=a_{11}a_{22}-a_{12}a_{21}$ is positive for valid cycles, as required by the paper’s inverse supply formulas. Sequential policies may contain any positive number of cycles, with either leading type in each; simultaneous policies are partitions of the full horizon. Indices 0 and 1 in Lean represent the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, pp. 7–13 (PDF 8–14), §3, §3.1, §3.2, Assumption 1

import Mathlib

namespace BundledExpansion.SeqSim

structure Params where
  T : ℝ
  A : ℝ
  a : Fin 2 → Fin 2 → ℝ
  c : Fin 2 → ℝ
  h : Fin 2 → ℝ
  d : Fin 2 → ℝ → ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.T ∧ 0 < P.A ∧ (∀ i, 0 < P.h i) ∧ (∀ i j, 0 < P.a i j) ∧
    ∀ i, ∀ t ∈ Set.Icc 0 P.T, 0 ≤ P.d i t

def Params.Regular (P : Params) : Prop :=
  ∀ i, ContinuousOn (P.d i) (Set.Icc 0 P.T)

def Params.RatioGuard (P : Params) : Prop :=
  ∀ t ∈ Set.Icc 0 P.T,
    P.a 0 1 * P.d 1 t < P.a 1 1 * P.d 0 t ∧
    P.a 1 0 * P.d 0 t < P.a 0 0 * P.d 1 t

noncomputable def D (P : Params) (i : Fin 2) (s t : ℝ) : ℝ :=
  ∫ u in s..t, P.d i u

noncomputable def F (P : Params) (i : Fin 2) (s t : ℝ) : ℝ :=
  ∫ u in s..t, D P i s u

def alpha (P : Params) : ℝ := P.a 0 0 * P.a 1 1 - P.a 0 1 * P.a 1 0

def w (P : Params) (j : Fin 2) : ℝ :=
  P.h 0 * P.a 0 j + P.h 1 * P.a 1 j

def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

structure Repl where
  time : ℝ
  q : Fin 2 → ℝ

noncomputable def excess (P : Params) (plan : List Repl) (s : ℝ)
    (i : Fin 2) (t : ℝ) : ℝ :=
  ((plan.filter (fun r => r.time ≤ t)).map
    (fun r => ∑ j : Fin 2, P.a i j * r.q j)).sum - D P i s t

noncomputable def holding (P : Params) (plan : List Repl) (s e : ℝ) : ℝ :=
  ∑ i : Fin 2, P.h i * ∫ t in s..e, excess P plan s i t

def purchase (P : Params) (plan : List Repl) : ℝ :=
  (plan.map (fun r => ∑ j : Fin 2, P.c j * r.q j)).sum

structure SeqCycle where
  start : ℝ
  stop : ℝ
  lead : Fin 2
  m : ℕ
  τ : ℕ → ℝ

def SeqCycle.follow (C : SeqCycle) : Fin 2 := other C.lead

noncomputable def SeqCycle.leadQ (P : Params) (C : SeqCycle) (k : ℕ) : ℝ :=
  D P C.follow (C.τ k) (C.τ (k + 1)) / P.a C.follow C.lead

noncomputable def SeqCycle.followQ (P : Params) (C : SeqCycle) : ℝ :=
  D P C.follow (C.τ C.m) C.stop / P.a C.follow C.follow

noncomputable def SeqCycle.plan (P : Params) (C : SeqCycle) : List Repl :=
  (List.range C.m).map (fun k =>
    ⟨C.τ k, fun j => if j = C.lead then C.leadQ P k else 0⟩) ++
    [⟨C.τ C.m, fun j => if j = C.follow then C.followQ P else 0⟩]

def SeqCycle.Assumption1 (P : Params) (C : SeqCycle) : Prop :=
  ∀ k < C.m,
    0 < D P 1 (C.τ k) (C.τ (k + 1)) ∧
    P.a 1 0 * D P 0 (C.τ k) (C.τ (k + 1)) ≤
      P.a 0 0 * D P 1 (C.τ k) (C.τ (k + 1)) ∧
    P.a 0 1 * D P 1 (C.τ k) (C.τ (k + 1)) ≤
      P.a 1 1 * D P 0 (C.τ k) (C.τ (k + 1))

def SeqCycle.Valid (P : Params) (C : SeqCycle) : Prop :=
  0 < alpha P ∧ 0 ≤ C.start ∧ C.stop ≤ P.T ∧
    1 ≤ C.m ∧ C.τ 0 = C.start ∧ C.τ (C.m + 1) = C.stop ∧
    (∀ k < C.m + 1, C.τ k < C.τ (k + 1)) ∧
    C.Assumption1 P ∧
    P.a C.lead C.lead * (∑ k ∈ Finset.range C.m, C.leadQ P k) +
      P.a C.lead C.follow * C.followQ P = D P C.lead C.start C.stop ∧
    (∀ t ∈ Set.Icc C.start C.stop, ∀ i : Fin 2,
      0 ≤ excess P (C.plan P) C.start i t)

noncomputable def SeqCycle.fixed (P : Params) (C : SeqCycle) : ℝ :=
  P.A * (C.m + 1)

noncomputable def SeqCycle.cost (P : Params) (C : SeqCycle) : ℝ :=
  C.fixed P + purchase P (C.plan P) + holding P (C.plan P) C.start C.stop

structure SeqPolicy where
  cycles : List SeqCycle

def SeqPolicy.Valid (P : Params) (S : SeqPolicy) : Prop :=
  S.cycles ≠ [] ∧
    S.cycles.head?.map SeqCycle.start = some 0 ∧
    S.cycles.getLast?.map SeqCycle.stop = some P.T ∧
    (∀ C ∈ S.cycles, C.Valid P) ∧
    (∀ p ∈ S.cycles.zip S.cycles.tail, p.1.stop = p.2.start)

noncomputable def SeqPolicy.cost (P : Params) (S : SeqPolicy) : ℝ :=
  (S.cycles.map (SeqCycle.cost P)).sum

noncomputable def optSeq (P : Params) : ℝ :=
  sInf {x : ℝ | ∃ S : SeqPolicy, S.Valid P ∧ x = S.cost P}

structure SimCycle where
  start : ℝ
  stop : ℝ
  K : ℕ
  τ : ℕ → ℝ

noncomputable def SimCycle.q (P : Params) (C : SimCycle) (k : ℕ)
    (j : Fin 2) : ℝ :=
  if j = 0 then
    (P.a 1 1 * D P 0 (C.τ k) (C.τ (k + 1)) -
      P.a 0 1 * D P 1 (C.τ k) (C.τ (k + 1))) / alpha P
  else
    (P.a 0 0 * D P 1 (C.τ k) (C.τ (k + 1)) -
      P.a 1 0 * D P 0 (C.τ k) (C.τ (k + 1))) / alpha P

noncomputable def SimCycle.plan (P : Params) (C : SimCycle) : List Repl :=
  (List.range C.K).map (fun k => ⟨C.τ k, C.q P k⟩)

def SimCycle.Valid (P : Params) (C : SimCycle) : Prop :=
  0 < alpha P ∧ 0 ≤ C.start ∧ C.stop ≤ P.T ∧
    1 ≤ C.K ∧ C.τ 0 = C.start ∧ C.τ C.K = C.stop ∧
    (∀ k < C.K, C.τ k < C.τ (k + 1)) ∧
    (∀ k < C.K, ∀ j : Fin 2, 0 ≤ C.q P k j) ∧
    (∀ k < C.K, ∀ i : Fin 2,
      (∑ j : Fin 2, P.a i j * C.q P k j) =
        D P i (C.τ k) (C.τ (k + 1))) ∧
    (∀ t ∈ Set.Icc C.start C.stop, ∀ i : Fin 2,
      0 ≤ excess P (C.plan P) C.start i t)

noncomputable def SimCycle.fixed (P : Params) (β : ℝ) (C : SimCycle) : ℝ :=
  β * P.A * C.K

noncomputable def SimCycle.cost (P : Params) (β : ℝ) (C : SimCycle) : ℝ :=
  C.fixed P β + purchase P (C.plan P) + holding P (C.plan P) C.start C.stop

def SimCycle.IsPolicy (P : Params) (C : SimCycle) : Prop :=
  C.Valid P ∧ C.start = 0 ∧ C.stop = P.T

noncomputable def optSim (P : Params) (β : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ C : SimCycle, C.IsPolicy P ∧ x = C.cost P β}

noncomputable def commonPurchase (P : Params) (s e : ℝ) : ℝ :=
  ((P.c 0 * P.a 1 1 - P.c 1 * P.a 1 0) * D P 0 s e +
    (P.c 1 * P.a 0 0 - P.c 0 * P.a 0 1) * D P 1 s e) / alpha P

noncomputable def psi (P : Params) (C : SeqCycle) : ℝ :=
  ∑ i : Fin 2, P.h i *
    ((C.stop - C.τ C.m) * D P i C.start C.stop - F P i C.start C.stop)

end BundledExpansion.SeqSim


