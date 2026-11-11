-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Reduction
-- name    : MeanCertificates1424_Hardness_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:02.076967+00:00
-- url     : https://prove2.me/theorems/f7424a4f-0125-42d1-b261-c2066682e3a1
-- title:
--   The explicit replicated-edge and three-anchor reduction
-- statement:
--   Let $H$ have $r$ vertices and $m$ edges, let $2\le k\le r$, and let $R\ge1$ be an integer. Set $b=Rm+k$. Order the vertices as the $r$ original vertices, $R$ distinct replicas of each input edge, three independent anchor groups $A_0,A_1,A_2$ of size $b+1$, and $p$ additional vertices in $A_1$. Originals report zero, replicas report three, and anchor groups report their subscripts. Every vertex in $A_1$ joins every vertex outside $A_1$; $A_0$ joins every original; $A_2$ joins every replica; each replica joins its two original endpoints. There are no other edges, and the original edges of $H$ are not retained. The resulting instance has $L=1$, $\epsilon=0$, no audits, and
--
--   $$N=r+Rm+3(Rm+k+1)+p,\qquad b=Rm+k,\qquad B_0=Rm+3(b+1)+p.$$
--
--   For fixed rational $\rho>0$, choose $p=\max\{0,\lceil b/\rho\rceil-N_0\}$, where $N_0$ is the unpadded count. The output guarantees predicate records regularity, three-colorability, exact diameter two, $2b<N$, the report alphabet, the derived box bound on all feasible real fields, the two exact endpoints and their attainment, and the exact width. These are statements to prove about the computed gadget, never evidence supplied as input.
--
--   This construction fixes the object used throughout the reduction and hardness statements. It does not compute a densest subgraph or use an optimum in constructing the input instance.
--
--   **Formalization Note** Edge pairs are listed in increasing numeric endpoint code and each replica has its own index. Padding adds only middle-anchor vertices. The predicates apply the original continuous-field feasible class without a box constraint.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 3.1 and its proof, printed pp.7–8 (PDF pp.9–10)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Model

set_option autoImplicit false

namespace MeanCertificates1424.Hardness

/-- The concrete gadget in Theorem 3.1's proof, printed pp.7–8 (PDF pp.9–10).
Vertex order: originals; edge replicas; A0; A1 including padding; A2. -/
noncomputable def gadgetBudget {r : ℕ} (H : SimpleGraph (Fin r)) (k R : ℕ) : ℕ :=
  R * edgeCount H + k

noncomputable def gadgetSize {r : ℕ} (H : SimpleGraph (Fin r)) (k R p : ℕ) : ℕ :=
  r + R * edgeCount H + 3 * (gadgetBudget H k R + 1) + p

/-- Tags 0,1,2,3,4 stand for originals, replicas, A0, A1, A2.
The ranges are disjoint, so truncated subtraction below is used only in its own range. -/
noncomputable def gadgetTag {r : ℕ} (H : SimpleGraph (Fin r)) (k R p t : ℕ) : ℕ :=
  let b := gadgetBudget H k R
  let a := r + R * edgeCount H
  if t < r then 0 else if t < a then 1 else if t < a + b + 1 then 2
  else if t < a + 2 * (b + 1) + p then 3 else 4

/-- Replica (e,j), j<R, has index r+R*index(e)+j. Input edges are not retained. -/
noncomputable def incidentReplica {r : ℕ} (H : SimpleGraph (Fin r))
    (R t v : ℕ) : Prop :=
  ∃ e : ℕ,
    (((edgePairs H).image fun e => e.1.val * r + e.2.val).sort (· ≤ ·))[(t-r)/R]? = some e ∧
    (v = e / r ∨ v = e % r)

noncomputable def gadgetRel {r : ℕ} (H : SimpleGraph (Fin r))
    (k R p : ℕ) (i j : Fin (gadgetSize H k R p)) : Prop :=
  let ti := gadgetTag H k R p i.val
  let tj := gadgetTag H k R p j.val
  (ti = 3 ∧ tj ≠ 3) ∨
  (ti = 2 ∧ tj = 0) ∨ (ti = 4 ∧ tj = 1) ∨
  (ti = 1 ∧ tj = 0 ∧ incidentReplica H R i.val j.val)

/-- `fromRel` symmetrizes the listed joins and excludes loops. -/
noncomputable def gadgetGraph {r : ℕ} (H : SimpleGraph (Fin r))
    (k R p : ℕ) : SimpleGraph (Fin (gadgetSize H k R p)) :=
  SimpleGraph.fromRel (gadgetRel H k R p)

noncomputable def gadgetReport {r : ℕ} (H : SimpleGraph (Fin r))
    (k R p : ℕ) (v : Fin (gadgetSize H k R p)) : ℚ :=
  match gadgetTag H k R p v.val with
  | 1 => 3
  | 3 => 1
  | 4 => 2
  | _ => 0

noncomputable def gadget {r : ℕ} (H : SimpleGraph (Fin r))
    (k R p : ℕ) : UniformInstance :=
  ⟨gadgetSize H k R p, gadgetGraph H k R p, gadgetBudget H k R,
    1, 0, gadgetReport H k R p⟩

/-- Fixed-rational padding specified in the brief: max(0,ceil(b/ρ)−N0).
Only positive ρ is used in the theorem. Padding changes N and B0, never b. -/
noncomputable def padding {r : ℕ} (H : SimpleGraph (Fin r))
    (k R : ℕ) (ρ : ℚ) : ℕ :=
  Int.toNat (⌈(gadgetBudget H k R : ℚ) / ρ⌉ - (gadgetSize H k R 0 : ℤ))

noncomputable def baselineSum {r : ℕ} (H : SimpleGraph (Fin r)) (k R p : ℕ) : ℕ :=
  R * edgeCount H + 3 * (gadgetBudget H k R + 1) + p

/-- Mathematical output guarantees, all conclusions, never constructor inputs.
Both finite endpoints are attained by actual real-valued feasible fields. -/
noncomputable def GadgetGuarantees {r : ℕ} (H : SimpleGraph (Fin r))
    (k R p : ℕ) : Prop :=
  let I := gadget H k R p
  let B := baselineSum H k R p
  Regular I ∧ ThreeColorable I.graph ∧ DiameterTwo I.graph ∧
  2 * I.budget < I.n ∧
  (∀ v, I.reports v ∈ ({0, 1, 2, 3} : Finset ℚ)) ∧
  (∀ x ∈ feasible I, ∀ v, x v ∈ Set.Icc (0 : ℝ) 2) ∧
  lower I = (((B : ℝ) - 2 * k) / I.n : ℝ) ∧
  upper I = (((B : ℝ) + R * dks H k + k) / I.n : ℝ) ∧
  width I = (((R : ℝ) * dks H k + 3 * k) / I.n : ℝ) ∧
  (∃ x ∈ feasible I, (mean I x : EReal) = lower I) ∧
  (∃ x ∈ feasible I, (mean I x : EReal) = upper I)

end MeanCertificates1424.Hardness


