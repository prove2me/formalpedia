-- Prove2me | Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Model
-- name    : FlowJobHardness_FlowShopGap_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:24:29.029787+00:00
-- url     : https://prove2.me/theorems/a935897f-e64d-4b8f-9d41-6f0156a08829
-- title:
--   Shop classes, completion objectives and the load lower bound
-- statement:
--   Let $I$ be a finite job shop with nonnegative real operation durations and the published chain and machine feasibility constraints. A generalized flow shop visits a subsequence of one common machine order; a flow shop visits every machine in that order; an acyclic job shop visits each machine at most once.
--
--   For a feasible schedule $s$, let $C_j$ be the completion time of the last operation of job $j$. Define
--   $$\Sigma C_j=\sum_j C_j,\qquad \mathrm{lb}=\max\{\max_m \mathrm{load}_m,\max_j \mathrm{length}_j\}.$$
--   More than half of the $n$ jobs finish by $t$ precisely when $n<2|\{j:C_j\le t\}|$.
--
--   These predicates and objectives support the companion hardness statements. Empty jobs, machine sets and operation sets have zero associated maxima. Machine order is existential, with no permutation restriction on schedules. The common rank order is strict on operation indices, so jumps are allowed and revisits are excluded only in the flow subclasses.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, pp. 20:1–20:3, §1, Fig. 1 and §1.1

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

open JobShopLTAS.Core

/-- §1, pp. 20:1–20:3. A common machine order, represented by its rank bijection.
Strict increase permits skipped machines, and forbids revisits. -/
def IsGeneralizedFlowShop {m n : ℕ} (I : Instance m n) : Prop :=
  ∃ rank : Fin m ≃ Fin m, ∀ j (i k : Fin (I.μ j)), i < k →
    rank (I.π j i) < rank (I.π j k)

/-- The ordinary flow shop also visits every machine. -/
def IsFlowShop {m n : ℕ} (I : Instance m n) : Prop :=
  IsGeneralizedFlowShop I ∧ ∀ j, Function.Surjective (I.π j)

/-- Acyclic job shops may use different machine orders in different jobs. -/
def IsAcyclicJobShop {m n : ℕ} (I : Instance m n) : Prop :=
  ∀ j, Function.Injective (I.π j)

/-- Completion of the last operation; the finite maximum is equivalent under
chain precedence. Empty jobs have completion zero. -/
noncomputable def completion {m n : ℕ} (I : Instance m n)
    (s : I.Op → ℝ) (j : Fin n) : ℝ :=
  ⨆ i : Fin (I.μ j), s ⟨j, i⟩ + I.p j i

/-- The unweighted objective used in Theorems 1.3–1.4. -/
noncomputable def completionSum {m n : ℕ} (I : Instance m n) (s : I.Op → ℝ) : ℝ :=
  ∑ j, completion I s j

/-- Congestion versus dilation; finite empty maxima have value zero. -/
noncomputable def lowerBound {m n : ℕ} (I : Instance m n) : ℝ :=
  max I.Pmax (⨆ j : Fin n, I.jobLength j)

open Classical in
/-- Inclusive time endpoint and strict integer majority, including odd job counts. -/
noncomputable def moreThanHalfBy {m n : ℕ} (I : Instance m n)
    (s : I.Op → ℝ) (t : ℝ) : Prop :=
  n < 2 * (Finset.univ.filter fun j => completion I s j ≤ t).card

inductive Objective where
  | makespan
  | sumCompletion
  deriving DecidableEq

noncomputable def value {m n : ℕ} (I : Instance m n) (o : Objective)
    (s : I.Op → ℝ) : ℝ :=
  match o with
  | .makespan => I.makespan Finset.univ s
  | .sumCompletion => completionSum I s

end FlowJobHardness.FlowShopGap.Supplement


