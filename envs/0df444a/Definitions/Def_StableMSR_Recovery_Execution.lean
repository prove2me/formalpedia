-- Prove2me | Definitions.Def_StableMSR_Recovery_Execution
-- name    : StableMSR_Recovery_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:33.605071+00:00
-- url     : https://prove2.me/theorems/fca94fe1-e69c-4640-8a45-bf6f4377c943
-- title:
--   Deterministic execution and exact-k output decoding
-- statement:
--   A deterministic program is a finite admissible program of the published distance-table real RAM, with both random-input instructions forbidden. Each executed scalar instruction, comparison, load/store, distance lookup, branch, or halt costs one interpreter step. Literals are rational. The metric input itself may be any finite real metric.
--
--   The initial integer inputs are $n,k$; the wrapper's two extra scalar slots are fixed at zero and supply no instance advice. Output labels must lie in $\{0,\ldots,k-1\}$ and use every label. Their nonempty fibers form an unordered partition. The recovery predicate requires an actual halting execution within its budget and
--   $$
--   \mathcal P_{\mathrm{out}}\text{ is feasible},\qquad
--   \mathcal O\text{ is }\gamma\text{-stable}\ \Longrightarrow\ \mathcal P_{\mathrm{out}}=\mathcal O.
--   $$
--   This connects algorithmic existence to a finite instruction language and the actual output memory. **Formalization Note** The original input distance table is the only distance-lookup instruction; no instruction evaluates an arbitrary helper function, computes an optimum, or calls a treewidth oracle. Rational literals do not restrict the theorem's real input metrics or its real stability factor. This module does not yet provide rational bit-cost instrumentation.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), p. 2, Theorem 1.1; p. 4, computational model; p. 21, fixed rational parameter; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Model
import Definitions.Def_StableMSR_Recovery_Parameters
import Definitions.Def_MinSumFPT_Machine

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

/-- A finite syntactic program; every executed instruction is charged by the imported interpreter. -/
def DeterministicProgram (P : MinSumFPT.Program) : Prop :=
  MinSumFPT.Admissible P ∧ ∀ i ∈ P, match i with
    | .unif _ | .uniformIndex _ _ => False
    | _ => True

/-- Source inputs are n,k,d. The wrapper's two unused scalar inputs are fixed zeros.
The tape cannot be read by a DeterministicProgram. -/
noncomputable def execute (P : MinSumFPT.Program) (n k : ℕ)
    (d : Point n → Point n → ℝ) (t : ℕ) : MinSumFPT.State :=
  MinSumFPT.run P n k 0 0 d (fun _ => 0) t

/-- Decode unordered blocks from integer labels, validating labels separately below. -/
noncomputable def outputPartition (n k : ℕ) (s : MinSumFPT.State) : Partition n :=
  (Finset.univ : Finset (Fin k)).image (fun j =>
    (Finset.univ : Cluster n).filter (fun x => s.imem (-1 - (x.val : ℤ)) = (j.val : ℤ)))

def ValidLabels (n k : ℕ) (s : MinSumFPT.State) : Prop :=
  (∀ x : Point n, 0 ≤ s.imem (-1 - (x.val : ℤ)) ∧ s.imem (-1 - (x.val : ℤ)) < (k : ℤ)) ∧
  ∀ j : Fin k, ∃ x : Point n, s.imem (-1 - (x.val : ℤ)) = (j.val : ℤ)

noncomputable def RecoversWithin (P : MinSumFPT.Program) (n k : ℕ)
    (d : Point n → Point n → ℝ) (γ : ℝ) (budget : ℕ) : Prop :=
  ∃ t ≤ budget,
    let s := execute P n k d t
    s.halted = true ∧ s.work ≤ budget ∧ ValidLabels n k s ∧
      Feasible Finset.univ k (outputPartition n k s) ∧
      ∀ O, Stable d k γ O → outputPartition n k s = O

end StableMSR.Recovery


