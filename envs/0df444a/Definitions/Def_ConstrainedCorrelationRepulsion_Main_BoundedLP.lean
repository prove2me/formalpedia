-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_BoundedLP
-- name    : ConstrainedCorrelationRepulsion_Main_BoundedLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:49.653575+00:00
-- url     : https://prove2.me/theorems/8bf085b9-a417-41e7-93e2-c31940c762ac
-- title:
--   The r-bounded sub-cluster LP on whole units
-- statement:
--   For $s\in\{1,\ldots,n\}$ and $T\subseteq\mathcal U$ with $|T|\le r$, the variable $y_{s,T}$ records local inclusion mass. Coverage is one per unit. All local inclusion–exclusion inequalities hold, and the size identity is $\sum_D |D|y_{s,T\cup\{D\}}=s y_{s,T}$. Hard unit pairs have zero joint mass. Vertex separation values are $x_{uv}=1-\sum_s y_{s,\{B(u),B(v)\}}$.
--
--   Sizes count vertices. Empty-index variables can exceed one. There is no size-gap constraint, no assumed probability law on complete partitions, and no metric-feasibility axiom replacing these constraints. The domain outside the finite variable list is padded by zero. The LP objective, optimality predicate, rationality predicate, total mass $Z$, eligible units, and analytical conditional ratios are defined independently of sampling guarantees.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Definition 2.5, equations (2)–(6), §5.1; printed pp.9–10, 22–24 (PDF pp.10–11, 23–25)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Units

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

abbrev LocalTable (n : ℕ) := ℕ → Finset (Finset (Fin n)) → ℝ

noncomputable def tableDistance {n : ℕ} (U : Units n) (y : LocalTable n)
    (u v : Fin n) : ℝ :=
  1 - ∑ s ∈ Finset.Icc 1 n, y s {unitOf U u, unitOf U v}

/-- Definition 2.5, equations (2)–(6). Indices outside the finite variable domain are zero.
The size identities count vertices. There is no size-gap constraint and no distribution on
complete partitions. Metric feasibility is not an input assumption. -/
def BoundedFeasible {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) : Prop :=
  (∀ s T, ¬ (s ∈ Finset.Icc 1 n ∧ T ⊆ U.blocks ∧ T.card ≤ r) → y s T = 0) ∧
  (∀ B ∈ U.blocks, (∑ s ∈ Finset.Icc 1 n, y s {B}) = 1) ∧
  (∀ s ∈ Finset.Icc 1 n, ∀ S T : Finset (Finset (Fin n)),
    S ⊆ U.blocks → T ⊆ U.blocks → Disjoint S T → S.card + T.card ≤ r →
    0 ≤ ∑ Q ∈ T.powerset, (-1 : ℝ) ^ Q.card * y s (S ∪ Q)) ∧
  (∀ s ∈ Finset.Icc 1 n, ∀ T, T ⊆ U.blocks → T.card + 1 ≤ r →
    (∑ D ∈ U.blocks, (D.card : ℝ) * y s (insert D T)) = (s : ℝ) * y s T) ∧
  (∀ s ∈ Finset.Icc 1 n, ∀ B ∈ U.blocks, ∀ D ∈ U.blocks,
    HardProduct I B D → y s {B,D} = 0)

noncomputable def Lplus {n : ℕ} (I : Instance n) (U : Units n) (y : LocalTable n) : ℝ :=
  pairSum (fun u v => if I.positive.Adj u v then tableDistance U y u v else 0)

noncomputable def Lminus {n : ℕ} (I : Instance n) (U : Units n) (y : LocalTable n) : ℝ :=
  pairSum (fun u v => if I.positive.Adj u v then 0 else 1 - tableDistance U y u v)

noncomputable def L {n : ℕ} (I : Instance n) (U : Units n) (y : LocalTable n) : ℝ :=
  Lplus I U y + Lminus I U y

def BoundedOptimal {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) : Prop :=
  BoundedFeasible I U r y ∧ ∀ z, BoundedFeasible I U r z → L I U y ≤ L I U z

def RationalTable {n : ℕ} (y : LocalTable n) : Prop := ∀ s T, ∃ q : ℚ, (q : ℝ) = y s T

noncomputable def Z {n : ℕ} (y : LocalTable n) : ℝ := ∑ s ∈ Finset.Icc 1 n, y s ∅

noncomputable def eligible {n : ℕ} (I : Instance n) (U : Units n)
    (a : Fin n) : Finset (Finset (Fin n)) :=
  U.blocks.filter (fun D => D ≠ unitOf U a ∧ Compatible I D (unitOf U a))

noncomputable def conditionalValue {n : ℕ} (U : Units n) (y : LocalTable n) (s : ℕ)
    (a : Fin n) (seeds : List (Finset (Fin n))) (T : Finset (Finset (Fin n))) : ℝ :=
  let S := insert (unitOf U a) seeds.toFinset
  y s (S ∪ T) / y s S

end ConstrainedCorrelationRepulsion.Main


