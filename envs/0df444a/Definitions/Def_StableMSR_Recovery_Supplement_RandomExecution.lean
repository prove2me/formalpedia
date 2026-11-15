-- Prove2me | Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution
-- name    : StableMSR_Recovery_Supplement_RandomExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:11:00.214203+00:00
-- url     : https://prove2.me/theorems/166781c9-9946-4ded-9b4d-0417b33c00cc
-- title:
--   Random-tape execution and permutation-family outputs
-- statement:
--   A program is a finite admissible program of the published distance-table RAM. On input $(n,k,d)$ it executes with the two auxiliary scalar inputs fixed to zero and a tape $\omega:\mathbb N\to\mathbb R$. Output labels and the unordered partition are decoded by the published recovery interface.
--
--   $$
--   \operatorname{AlwaysFeasible}(P,n,k,d,T)\iff
--   \forall\omega\ \exists t\le T:\ \text{the run halts, charges at most }T\text{ work, and returns valid exact-}k\text{ labels}.
--   $$
--
--   Independent runs have the product of $m$ copies of the published tape law. A cheapest-output failure occurs when some minimum-cost output of the $m$ runs differs from the stable optimum; this includes every tie-breaking rule. For permutation enumeration, a family is a nonempty list of lists, each a permutation of $0,\ldots,m-1$. Its first-element probability is the number of successful list occurrences divided by the list length.
--
--   This interface supplies charged executions and literal multiset probabilities. **Formalization Note** The deterministic predicate, interpreter, tape law, and output decoders are reused. No field assigns a runtime or supplies an optimum oracle.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), p. 4 computational model, Theorem 4.5 p. 11, Appendix A.5 p. 21, Theorem B.2 p. 23; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

abbrev Tape := ℕ → ℝ

noncomputable def randomState (P : MinSumFPT.Program) (n k : ℕ)
    (d : Point n → Point n → ℝ) (ω : Tape) (budget : ℕ) : MinSumFPT.State :=
  MinSumFPT.run P n k 0 0 d ω budget

noncomputable def randomOutput (P : MinSumFPT.Program) (n k : ℕ)
    (d : Point n → Point n → ℝ) (budget : ℕ) (ω : Tape) : Partition n :=
  outputPartition n k (randomState P n k d ω budget)

noncomputable def AlwaysFeasible (P : MinSumFPT.Program) (n k : ℕ)
    (d : Point n → Point n → ℝ) (budget : ℕ) : Prop :=
  ∀ ω, ∃ t ≤ budget,
    let s := randomState P n k d ω t
    s.halted = true ∧ s.work ≤ budget ∧ ValidLabels n k s ∧
      Feasible Finset.univ k (outputPartition n k s)

noncomputable def independentTapes (m : ℕ) : MeasureTheory.Measure (Fin m → Tape) :=
  MeasureTheory.Measure.pi (fun _ => MinSumFPT.tapeLaw)

/-- Failure of some minimum-cost output; quantifies over every way of breaking ties. -/
noncomputable def CheapestFailure (P : MinSumFPT.Program) (n k : ℕ)
    (d : Point n → Point n → ℝ) (budget m : ℕ) (O : Partition n) (ω : Fin m → Tape) : Prop :=
  ∃ i : Fin m, (∀ j : Fin m,
    cost d (randomOutput P n k d budget (ω i)) ≤ cost d (randomOutput P n k d budget (ω j))) ∧
    randomOutput P n k d budget (ω i) ≠ O

/-- An output list of permutations, retaining every occurrence. -/
def PermutationFamily (m : ℕ) (F : List (List ℤ)) : Prop :=
  F ≠ [] ∧ ∀ π ∈ F, π.Perm ((List.range m).map (fun j => (j : ℤ)))

def FirstIn (T : Finset ℕ) (z : ℕ) (π : List ℤ) : Prop :=
  ∀ y ∈ T, y ≠ z → π.idxOf (z : ℤ) < π.idxOf (y : ℤ)

noncomputable def firstFraction (F : List (List ℤ)) (T : Finset ℕ) (z : ℕ) : ℝ :=
  ((F.filter (fun π => FirstIn T z π)).length : ℝ) / F.length

end StableMSR.Recovery.Supplement


