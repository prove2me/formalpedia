-- Prove2me | Definitions.Def_LindbladStructLearn_Supplement_Session
-- name    : LindbladStructLearn_Supplement_Session
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:41:32.293483+00:00
-- url     : https://prove2.me/theorems/eccc6eaf-d91a-4289-8e10-b3726e57bcba
-- title:
--   Input layout, expectations of runs, and the interactive estimation session of Theorem 5.5
-- statement:
--   Theorem 5.5 asks for estimates $\widehat{\mathcal F}(x)$ at the iterates $x$ of Algorithm 4. Each iterate depends on the estimates already returned. This module models such an interaction on the published learner's machine (a real RAM with Pauli experiments):
--
--   1. `listInput`: the starting configuration with given integers and reals in the first memory cells and $0$ elsewhere.
--   2. `wexp`: the expectation of a function of the configuration reached after $N$ steps, the sum over runs of the products of branch probabilities. On an indicator it equals the published `mass`.
--   3. `feedPoint`: resuming a halted learner with a query point $x$. The learner's halt pointer points to its output block of records naming pairs of Paulis. Into the value cells of each valid record the environment writes the entry $x_Q$ of the pair $Q$ that record names. It then clears the output, and execution resumes after the `halt`.
--   4. `SessReach` and `sessionExp`: runs of $r$ rounds, and expectations over them. In round $j$ the point $x^{(j)}=\mathrm{next}(\widehat{\mathcal F}_0,\dots,\widehat{\mathcal F}_{j-1})$ is fed, the learner runs for $N$ steps, and it must halt. Its decoded output is $\widehat{\mathcal F}_j$.
--
--   The machine state, including the work count and the list of evolution durations, persists across rounds. Resource bounds on the final configuration therefore cover the whole session.
--
--   **Formalization Note** The learner receives all of $x$ by listing every $k$-local pair in its output block. A round that has not halted within $N$ steps contributes $0$ to `sessionExp`.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 5.5 and its proof, pp.40–42; machine of Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LindbladStructLearn_Reach
import Definitions.Def_LindbladStructLearn_Halted
import Definitions.Def_LindbladStructLearn_initState
import Definitions.Def_LindbladStructLearn_decode
import Definitions.Def_LindbladStructLearn_Idx
import Definitions.Def_LindbladStructLearn_toIdx
import Definitions.Def_LindbladStructLearn_ext

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing LindbladStructLearn

/-- An input configuration of the learner's machine (Lewis–Tang–Wright, *Learning the structure of
open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorems 5.5, 5.13,
5.18): the listed integers in integer cells `0, 1, …`, the listed reals in real cells `0, 1, …`, every
other cell `0` (as the published `goalInput`). The unknown dynamics is never part of the input. -/
noncomputable def listInput (ints : List ℤ) (reals : List ℝ) : MState :=
  initState (fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0)
    (fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0)

/-- The expectation of `f` over the configuration reached after exactly `N` steps from `s`: the
weighted sum over runs of the products of branch weights (the published `mass` is the case of an
indicator). Machine of Theorem 1.1, p.4; halted configurations stutter. -/
noncomputable def wexp (P : Program) (n : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n)) :
    ℕ → MState → (MState → ℝ≥0∞) → ℝ≥0∞
  | 0, s, f => f s
  | N + 1, s, f => ((branches P n evo s).map fun b => b.1 * wexp P n evo N b.2 f).sum

/-- Resuming a halted learner with a query point `x` (the interface of Theorem 5.5, p.40: estimates
`F̂(x)` "for given inputs `x`", one call per iteration of Algorithm 4).

If `s` has halted with output pointer `p`, the output block at `p` is read as in the published
`decode`: a count `K` (integer cell `p`) and records `j < K` at `b_j = p + 1 + j(3k + 3)`. Into every
valid record (its pair `Q` decoded by `recordPair`) the environment writes the query entry `x_Q`
(`0` if `Q` is not a `k`-local pair with `Q₁ ≠ I`): real part to real cell `b_j + 3k + 1`, imaginary
part to `b_j + 3k + 2`. All other cells are unchanged, the output is cleared, and execution resumes at
the instruction after the `halt`. A configuration that has not halted is unchanged.

**Formalization Note** The learner chooses which pairs it lists, so it receives `x` in full by listing
every `k`-local pair; the output of the round is then decoded from the next `halt` as usual. -/
noncomputable def feedPoint (n k : ℕ) (x : Idx n k → ℂ) (s : MState) : MState := by
  classical
  exact
  match s.output with
  | none => s
  | some p =>
    let K : ℕ := (s.intMem p).toNat
    let b : ℕ → ℤ := fun j => p + 1 + (j : ℤ) * (3 * k + 3)
    let valid : ℕ → Prop := fun j => (recordPair n k s.intMem (b j)).isSome
    let val : ℕ → ℂ := fun j =>
      match recordPair n k s.intMem (b j) with
      | some Q => ext x Q
      | none => 0
    { s with
      output := none
      core := { s.core with
        mem := fun z =>
          if ∃ j < K, valid j ∧ (z = b j + 3 * k + 1 ∨ z = b j + 3 * k + 2) then
            ∑ j ∈ Finset.range K,
              ((if valid j ∧ z = b j + 3 * k + 1 then (val j).re else 0) +
                (if valid j ∧ z = b j + 3 * k + 2 then (val j).im else 0))
          else s.core.mem z } }

/-- Runs of an interactive estimation session (Theorem 5.5, p.40). From a halted configuration `s`
with revealed estimates `h` (oldest first), one round feeds the query point `next h` (`feedPoint`),
runs the machine for `N` steps and must reach a halted configuration `s₁`, whose decoded output
`toIdx (decode n k s₁)` is the round's estimate. `SessReach … r h s h' s'` holds when `r` such rounds
lead from `(h, s)` to `(h', s')` through branches of positive weight (the published `Reach`). -/
def SessReach (P : Program) (n k : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n)) (N : ℕ)
    (next : List (Idx n k → ℂ) → Idx n k → ℂ) :
    ℕ → List (Idx n k → ℂ) → MState → List (Idx n k → ℂ) → MState → Prop
  | 0, h, s, h', s' => h' = h ∧ s' = s
  | r + 1, h, s, h', s' => ∃ s₁, Reach P n evo N (feedPoint n k (next h) s) s₁ ∧ Halted s₁ ∧
      SessReach P n k evo N next r (h ++ [toIdx (decode n k s₁)]) s₁ h' s'

/-- The expectation of `f(h', s')` over the outcome `(h', s')` of `r` session rounds from `(h, s)`
(Theorem 5.5, p.40; rounds as in `SessReach`). A round that has not halted after `N` steps
contributes `0`. -/
noncomputable def sessionExp (P : Program) (n k : ℕ) (evo : ℝ → Super (Qubits n) (Qubits n))
    (N : ℕ) (next : List (Idx n k → ℂ) → Idx n k → ℂ)
    (f : List (Idx n k → ℂ) → MState → ℝ≥0∞) :
    ℕ → List (Idx n k → ℂ) → MState → ℝ≥0∞
  | 0, h, s => f h s
  | r + 1, h, s => by
    classical
    exact wexp P n evo N (feedPoint n k (next h) s) fun s₁ =>
      if Halted s₁ then sessionExp P n k evo N next f r (h ++ [toIdx (decode n k s₁)]) s₁ else 0

end LindbladStructLearn.Supplement


