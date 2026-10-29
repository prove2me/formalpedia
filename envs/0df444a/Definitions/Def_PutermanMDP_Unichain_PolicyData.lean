-- Prove2me | Definitions.Def_PutermanMDP_Unichain_PolicyData
-- name    : PutermanMDP_Unichain_PolicyData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:49.877456+00:00
-- url     : https://prove2.me/theorems/1c132ca6-577a-4d2a-b491-28911762aca3
-- title:
--   Stationary-policy matrices, canonical bias and transient blocks
-- statement:
--   Let $M$ be a finite stationary Markov decision process, with nonempty admissible action sets $A_s$, rewards $r(s,a)$ and stochastic transition rows $p(j\mid s,a)$. An admissible decision rule $d$ chooses an action in $A_s$ at each state. Its reward vector is $r_d(s)=r(s,d(s))$ and its transition matrix is $P_d(i,j)=p(j\mid i,d(i))$.
--
--   The limiting and deviation matrices are the published finite-chain objects
--   $$P_d^*=\lim_{N\to\infty}\frac{1}{N+1}\sum_{k=0}^N P_d^k,\qquad H_d=(I-P_d+P_d^*)^{-1}-P_d^*,$$
--   and the canonical bias is $h^{d^\infty}=H_dr_d$. The expression for $H_d$ equals Puterman's $(I-P_d+P_d^*)^{-1}(I-P_d^*)$ for stochastic matrices. No aperiodicity is assumed. The identity $P_d^*h^{d^\infty}=0$ is a consequence of these definitions, not an input field.
--
--   Transient states are the complement of the recurrent states, with recurrence expressed by return accessibility in the finite chain. A transient block restricts both matrix indices to this subset; the transient resolvent is $(I-P_d^{TT})^{-1}$. The transient set may be empty.
--
--   These definitions extend the published MDP and Markov-chain objects without redefining either. **Formalization Note** Matrix inverses and limits are total Lean functions. For finite stochastic matrices the limits exist and the matrices inverted here are nonsingular; these mathematical facts are not assumed as model data.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, pp. 337–338 (PDF 353–354), (8.2.1)–(8.2.2); pp. 381–382 (PDF 397–398), (8.6.11)–(8.6.13); Appendix A.4–A.5, pp. 591–598 (PDF 607–614)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
open MarkovDecisionProcesses Matrix

namespace PutermanMDP.Unichain

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- An admissible deterministic stationary decision rule. -/
abbrev Rule (M : StationaryMDP S A) := {d : S → A // ∀ s, d s ∈ M.admissible s}

/-- The policy reward vector. -/
def policyReward (M : StationaryMDP S A) (d : Rule M) : S → ℝ :=
  fun s => M.reward s (d.val s)

/-- The Cesàro limiting matrix, including periodic chains (Appendix A.4). -/
noncomputable def policyLimit (M : StationaryMDP S A) (d : Rule M) : Matrix S S ℝ :=
  BlackwellDiscreteDP.NearOne.limitMatrix (transMatrix M d.val)

/-- The deviation matrix of Appendix A.5, (A.14). For stochastic matrices the
published expression `(I - P + P*)⁻¹ - P*` equals `(I - P + P*)⁻¹ (I - P*)`. -/
noncomputable def policyDeviation (M : StationaryMDP S A) (d : Rule M) : Matrix S S ℝ :=
  BlackwellDiscreteDP.NearOne.deviationMatrix (transMatrix M d.val)

/-- Canonical bias `h^{d^∞} = H_d r_d`, (8.2.2), with `P_d* h^{d^∞} = 0`.
The normalization is a consequence, not an assumed property. -/
noncomputable def policyBias (M : StationaryMDP S A) (d : Rule M) : S → ℝ :=
  (policyDeviation M d).mulVec (policyReward M d)

/-- Transient states of a finite chain, the complement of the recurrent states. -/
abbrev TransientStates (P : Matrix S S ℝ) := {s : S // ¬ IsRecurrent P s}

noncomputable instance transientStatesFintype (P : Matrix S S ℝ) :
    Fintype (TransientStates P) := Fintype.ofFinite _

instance transientStatesDecidableEq (P : Matrix S S ℝ) :
    DecidableEq (TransientStates P) := inferInstanceAs (DecidableEq {s : S // ¬ IsRecurrent P s})

/-- Restrict the rows and columns of `Q` to the transient states of `P`. -/
def transientBlock (P Q : Matrix S S ℝ) :
    Matrix (TransientStates P) (TransientStates P) ℝ :=
  fun i j => Q i.val j.val

/-- The inverse of `I - P^{TT}`, on the actual transient-state subtype. -/
noncomputable def transientResolvent (P : Matrix S S ℝ) :
    Matrix (TransientStates P) (TransientStates P) ℝ := by
  classical
  exact (1 - transientBlock P P)⁻¹

end PutermanMDP.Unichain


