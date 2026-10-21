-- Prove2me | Definitions.Def_HeteroBass_HetP_Model
-- name    : HeteroBass_HetP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:26.944837+00:00
-- url     : https://prove2.me/theorems/a77b0e77-2530-4517-937c-31ace85cfc90
-- title:
--   Heterogeneous discrete Bass adoption model
-- statement:
--   There are $M$ consumers. The adopter state is a set $S$; a nonadopter $j$ joins it at rate
--
--   $$p_j+\sum_{k\in S}q_{k,j}.$$
--
--   The transition matrix is $\exp(tG)$ for this chain’s generator, initially at $S=\varnothing$. The expected adopted fraction is $f(t)=M^{-1}\sum_S |S|\exp(tG)[\varnothing,S]$. On a complete network, incoming influence $q_j$ is divided equally among the $M-1$ peers. The arithmetic mean of node parameters supplies the homogeneous comparison.
--
--   Adoption-order permutations and their jump probabilities also define the CDFs of inter-adoption times and of the $m$th adoption time. These definitions support the comparison milestones.
--
--   **Formalization Note** The order stages are zero-based in Lean; stage $k$ is the paper’s $(k+1)$st waiting time. Path probabilities and exponential holding-time measures are used only under positive-stage-rate hypotheses.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, §2, eqs. (4)–(12), pp. 4–6; §3.3, (32), p. 10; §4, (34)–(35), p. 11

import Mathlib
import Definitions.Def_HeteroBass_HetP_finiteJumpGenerator

namespace HeteroBass.HetP

open MeasureTheory ProbabilityTheory

variable {M : ℕ}

/-- (5): rate of adoption by a non-adopter `j` when the adopter set is `S`. -/
noncomputable def adoptRate (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (S : Finset (Fin M)) (j : Fin M) : ℝ :=
  p j + ∑ k ∈ S, Q k j

/-- Total rate of leaving adopter set `S`. -/
noncomputable def totalRate (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (S : Finset (Fin M)) : ℝ :=
  ∑ j ∈ Sᶜ, adoptRate p Q S j

/-- Rate of a jump from adopter set `S` to adopter set `T`. -/
noncomputable def adopterJumpRate (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (S T : Finset (Fin M)) : ℝ :=
  ∑ j ∈ Sᶜ, if T = insert j S then adoptRate p Q S j else 0

/-- Generator of (5), on the finite space of adopter sets. -/
noncomputable def generator (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) :
    Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ :=
  finiteJumpGenerator (adopterJumpRate p Q)

/-- Transition matrix at time `t`, starting from any adopter set. -/
noncomputable def transition (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (t : ℝ) :
    Matrix (Finset (Fin M)) (Finset (Fin M)) ℝ :=
  NormedSpace.exp (t • generator p Q)

/-- (10)–(11): expected adopted fraction, initially with no adopters. -/
noncomputable def expectedFraction (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (t : ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ S : Finset (Fin M), (S.card : ℝ) * transition p Q t ∅ S

/-- (9) on a complete graph: incoming influence `q j` is shared among the `M-1` peers. -/
noncomputable def completeQ (q : Fin M → ℝ) : Fin M → Fin M → ℝ :=
  fun k j => if k = j then 0 else q j / ((M : ℝ) - 1)

/-- (34): arithmetic mean of the node parameters. -/
noncomputable def mean (x : Fin M → ℝ) : ℝ :=
  (∑ i, x i) / (M : ℝ)

/-- The adopters preceding the zero-based stage `k` in order `sigma`. -/
def stageSet (sigma : Equiv.Perm (Fin M)) (k : ℕ) : Finset (Fin M) :=
  (Finset.univ.filter (fun i : Fin M => i.val < k)).image sigma

/-- Total adoption rate at zero-based stage `k`. -/
noncomputable def stageRate (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (sigma : Equiv.Perm (Fin M)) (k : Fin M) : ℝ :=
  totalRate p Q (stageSet sigma k.val)

/-- Probability of an adoption order, when its stage rates are positive. -/
noncomputable def pathWeight (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (sigma : Equiv.Perm (Fin M)) : ℝ :=
  ∏ k : Fin M, adoptRate p Q (stageSet sigma k.val) (sigma k) / stageRate p Q sigma k

/-- CDF of the holding time at zero-based stage `k`, mixed over adoption orders. -/
noncomputable def interCDF (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (k : Fin M) (tau : ℝ) : ℝ :=
  ∑ sigma : Equiv.Perm (Fin M),
    pathWeight p Q sigma * (1 - Real.exp (-(stageRate p Q sigma k) * tau))

/-- CDF of the time of adoption `m`: the first `m` independent exponential holding times,
mixed over adoption orders. `m` is the paper's one-based adoption number. -/
noncomputable def adoptionTimeCDF (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ)
    (m : ℕ) (t : ℝ) : ℝ :=
  ∑ sigma : Equiv.Perm (Fin M), pathWeight p Q sigma *
    ((Measure.pi (fun k : Fin M => expMeasure (stageRate p Q sigma k)))
      {x | ∑ k ∈ Finset.univ.filter (fun k : Fin M => k.val < m), x k ≤ t}).toReal

end HeteroBass.HetP


