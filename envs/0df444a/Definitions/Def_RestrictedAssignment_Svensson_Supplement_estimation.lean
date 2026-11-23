-- Prove2me | Definitions.Def_RestrictedAssignment_Svensson_Supplement_estimation
-- name    : RestrictedAssignment_Svensson_Supplement_estimation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:57:15.387304+00:00
-- url     : https://prove2.me/theorems/b614c36d-1c84-40a3-a205-1cffa7b78122
-- title:
--   Binary scheduling inputs and numerical-estimation specification
-- statement:
--   A binary instance consists of arbitrary finite job and machine counts, one nonnegative rational size per job, and a list of eligible machines for each job. The mathematical instance has jobs $\{0,\ldots,n-1\}$, machines $\{0,\ldots,m-1\}$, and the rational sizes cast to real numbers in the published model. Feasibility means that an eligible total schedule exists.
--
--   Counts, machine indices, and reduced rational numerators and denominators are encoded in binary. Sign bits, field separators, eligibility-list lengths, and a final terminator make the input and rational output unambiguous. The input length is the length of this concrete serialization. There is no bound on counts, eligibility lists, or bit lengths.
--
--   For a real tolerance $\varepsilon$ and rational numerical output $L$, the specification is
--   $$0\le L\le\mathrm{OPT}\le(33/17+\varepsilon)L.$$
--   Here OPT is the finite scheduling minimum, not a supplied input. In particular zero optimum forces $L=0$. The polynomial-time theorem uses the published deterministic multi-stack Turing machine and its operational step relation. Correctness and runtime concern the domain of feasible encoded instances; no behavior on malformed words or infeasible instances is promised. These definitions specify input and output meaning without assuming an algorithm or LP oracle.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, p. 2, Theorem 1.1; pp. 3–4, computation of OPT_LP; p. 11, accuracy loss

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_Supplement_optima
import Definitions.Def_IntConeFPT_Machine

namespace RestrictedAssignment.Svensson.Supplement

/-- Finite rational-input instances. The counts and all numerator/denominator bit
lengths are unrestricted. Empty eligibility lists are permitted. -/
structure BinaryInstance where
  jobs : ℕ
  machines : ℕ
  size : Fin jobs → ℚ
  size_nonneg : ∀ j, 0 ≤ size j
  allowed : Fin jobs → Finset (Fin machines)

/-- Decode rational sizes into the published real-valued scheduling model. -/
def BinaryInstance.realSize (I : BinaryInstance) (j : Fin I.jobs) : ℝ := I.size j

/-- A promise domain: precisely the instances admitting an eligible total schedule. -/
def BinaryInstance.Feasible (I : BinaryInstance) : Prop :=
  ∃ σ : Fin I.jobs → Fin I.machines, ∀ j, σ j ∈ I.allowed j

/-- Binary numeral followed by separator 2; `encodeNat` is Mathlib's injective
binary natural encoding, not a unary encoding. -/
def natCode (n : ℕ) : List OnlineCRS.Combine.Sym :=
  (Computability.encodeNat n).map (fun b => if b then 1 else 0) ++ [2]

/-- Sign, binary absolute numerator, and binary positive denominator. -/
def ratCode (q : ℚ) : List OnlineCRS.Combine.Sym :=
  [if q < 0 then 1 else 0] ++ natCode q.num.natAbs ++ natCode q.den

/-- Job and machine counts, then one row per indexed job: rational size,
cardinality of its eligibility list, and increasing binary machine indices.
The final separator 3 ends the instance. No exponential padding. -/
def BinaryInstance.code (I : BinaryInstance) : List OnlineCRS.Combine.Sym :=
  natCode I.jobs ++ natCode I.machines ++
    (List.finRange I.jobs).flatMap (fun j =>
      ratCode (I.size j) ++ natCode (I.allowed j).card ++
        ((I.allowed j).sort (· ≤ ·)).flatMap (fun i => natCode i.val)) ++ [3]

/-- Numerical output uses the same charged tape alphabet and binary rational code. -/
def estimateCode (q : ℚ) : List OnlineCRS.Combine.Sym := ratCode q ++ [3]

/-- A lower estimate with the source's multiplicative guarantee. `OPT` is computed
from all eligible schedules. No optimum, LP oracle, or execution cost is an input. -/
noncomputable def IsEstimate (I : BinaryInstance) (ε : ℝ) (L : ℚ) : Prop :=
  0 ≤ L ∧ ∃ v : ℝ, optimalMakespan I.allowed I.realSize = some v ∧
    (L : ℝ) ≤ v ∧ v ≤ (33 / 17 + ε) * (L : ℝ)

end RestrictedAssignment.Svensson.Supplement


