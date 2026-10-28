-- Prove2me | Definitions.Def_CountingMatroid_Model_Subroutines
-- name    : CountingMatroid_Model_Subroutines
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:39:16.021819+00:00
-- url     : https://prove2.me/theorems/30a53b70-2a0e-4f66-bd08-d9533abcee24
-- title:
--   Charged rank scans and a feasibility-solver contract
-- statement:
--   Let $[n]=\{0,\ldots,n-1\}$, with $n\in\mathbb N$. A Boolean oracle on subsets of $[n]$ answers encoded independence queries. For an oracle $o$, a target $A\subseteq[n]$, and a Boolean flag selecting the first or second oracle charge, `greedyRank` scans the elements in order, starts with the empty selected set, and retains a candidate insertion precisely when $o$ accepts it. It returns the number of retained elements as a charged computation; no oracle-correctness assumption is built into this operation.
--
--   For a paired state $S\subseteq[n]\times\{0,1\}$, set $X=\{i:(i,0)\in S\}$ and $Y=\{i:(i,1)\in S\}$. The charged projection scan returns $(X,[n]\setminus Y,|Y|)$. Given $r\in\mathbb N$ and two oracles $o_1,o_2$, the paired-rank routine evaluates
--   $$\operatorname{pairedRank}(S)=\operatorname{greedyRank}_{o_1}(X)+|Y|+\operatorname{greedyRank}_{o_2}([n]\setminus Y)-r,$$
--   where subtraction is truncated at zero. All scans retain the charges of their constituent operations.
--
--   For any charged computation $F$ with operation-count function $\operatorname{cost}_F$, define
--   $$Q(F)=\operatorname{cost}_F(\mathrm{oracleFirst})+\operatorname{cost}_F(\mathrm{oracleSecond}),$$
--   $$W(F)=\operatorname{cost}_F(\mathrm{fairBit})+\sum_{a\in\mathcal I}\operatorname{cost}_F(\mathrm{word}(a)),$$
--   where $\mathcal I$ is the model’s finite list of named instruction tags. These are `oracleCalls` and `otherSteps`.
--
--   A `FeasibilityImplementation` supplies a charged Boolean procedure $F(n,r,o_1,o_2)$. Its correctness predicate requires that whenever matroids $M_1,M_2$ have full ground set $[n]$, both have rank $r$, and the supplied oracles exactly decide their independent sets, the returned Boolean is true exactly when the number of common bases is positive. For natural constants $C_Q,d_Q,C_W,d_W$, its boundedness predicate requires, for every $n,r$ and every pair of oracle functions,
--   $$Q(F(n,r,o_1,o_2))\le C_Q(n+r+1)^{d_Q},\qquad W(F(n,r,o_1,o_2))\le C_W(n+r+1)^{d_W}.$$
--   A `FeasibilityContract` packages an implementation, these four constants, and proofs of the two predicates. This bundle defines the subroutine interface and its obligations; the contract type alone supplies no instance or existence proof.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Model/Subroutines.lean#L46-L139

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

section


set_option autoImplicit false

/-!
# Subroutine interfaces and unresolved executable dependencies

Correspondence ledger:

* main.tex:283–293, 1529–1534: deterministic matroid-intersection feasibility
  pretest. `FeasibilityImplementation.run` is its **explicit missing charged code**;
  `FeasibilityContract` records its exact decision and separate polynomial call
  and bit-work obligations. Inputs are `n`, `r`, and exactly two fixed n-bit
  independence oracles. Validity requires `CommonRank` and both `ExactOracle`
  promises, and `FullGround`. Output is a Boolean saying whether
  `commonBaseCount > 0`. No installed
  Mathlib or Arlib executable matroid-intersection implementation or cost
  certificate was found. This is a borrowed algorithmic dependency cited by the
  paper, not an extra feasibility oracle and not a theorem proved here. A later
  pass must provide concrete code and a RAM realization before using the
  contract; no instance or `Classical.choose` is supplied.
* main.tex:1333–1346: `greedyRank`, `pairedProjections`, and `pairedRank`
  implement the original-oracle greedy scan and formula. Correctness against
  Mathlib rank and the RAM realization are same-paper **proof obligations**;
  no paired-rank oracle or abstract whole-step field is introduced.
* main.tex:746–751, 1163–1205, 1392–1421, 1442–1448: exchange transition,
  capped trace restart, phase observation/update, bounded rejection draws, and
  median amplification are the reduction's own composition. They have no
  subroutine implementation parameter here; Program writes their loops and
  abort branches explicitly.

`Arlib.Computation.StdImpl` is only a price table. This installed Arlib pin has
`RAM` but no `Realizes`, `StdRealizes`, `Buffer`, `WordLoop`, `Matrix`, or
`SignedWord` realization layer. Thus even a future charged feasibility solver
will still need a representation relation, RAM code, correctness, execution
cost, word/address bounds, initialization, allocation, and physical-capacity
proofs. Exact fair-bit output laws belong in Run, not this deterministic file.
-/

namespace CountingMatroid.Model.Subroutines

open CountingMatroid.Model
open CountingMatroid.Model.Operations

/-- Greedy rank of a represented subset, with at most one original-oracle query
per ground element. The body constructs each n-bit candidate query explicitly.
Its mathematical rank identity and RAM realization remain proof obligations. -/
def greedyRank {n : ℕ} (which : Bool) (oracle : IndependenceOracle n)
    (target : Finset (Fin n)) : Arlib.Computation.Charged Op Cell ℕ := do
  let result ← Arlib.Computation.Charged.foldl (fun acc i => do
    let present ← containsElement target i
    if present then
      let candidate ← insertElement acc.1 i
      let q ← encodeQuery candidate
      let independent ← oracleQuery which oracle q
      if independent then
        let size ← successor acc.2
        pure (candidate, size)
      else pure acc
    else pure acc) (List.finRange n) ((∅ : Finset (Fin n)), 0)
  pure result.2

/-- Scan a paired state into its x projection, the complement of its y
projection, and the number of present y elements. Every membership and insert
is routed through the charged operation vocabulary. -/
def pairedProjections {n : ℕ} (state : PairedSet n) :
    Arlib.Computation.Charged Op Cell
      (Finset (Fin n) × Finset (Fin n) × ℕ) :=
  Arlib.Computation.Charged.foldl (fun acc i => do
    let inX ← containsPaired state (i, false)
    let x ← if inX then insertElement acc.1 i else pure acc.1
    let inY ← containsPaired state (i, true)
    if inY then
      let ysize ← successor acc.2.2
      pure (x, acc.2.1, ysize)
    else
      let complementY ← insertElement acc.2.1 i
      pure (x, complementY, acc.2.2))
    (List.finRange n) ((∅ : Finset (Fin n)), (∅ : Finset (Fin n)), 0)

/-- The paper's paired-rank formula, evaluated through the two original
independence oracles. Correctness against `M₁ ⊕ M₂*` is still to be proved. -/
def pairedRank {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (state : PairedSet n) : Arlib.Computation.Charged Op Cell ℕ := do
  let (x, complementY, ysize) ← pairedProjections state
  let rankX ← greedyRank false o₁ x
  let rankComplementY ← greedyRank true o₂ complementY
  let left ← natAdd rankX ysize
  let total ← natAdd left rankComplementY
  natSub total r

/-- An unresolved implementation parameter for the paper's cited deterministic
matroid-intersection pretest. It receives only the two original oracles. -/
structure FeasibilityImplementation where
  run : (n r : ℕ) → IndependenceOracle n → IndependenceOracle n →
    Arlib.Computation.Charged Op Cell Bool

/-- The number of original independence-oracle calls in the charged trace. -/
def oracleCalls {α : Type} (p : Arlib.Computation.Charged Op Cell α) : ℕ :=
  p.cost Op.oracleFirst + p.cost Op.oracleSecond

/-- The nonoracle primitive count: a fair-bit read or one named RAM instruction.
A bit-cost theorem additionally needs a concrete bounded-word realization. -/
def otherSteps {α : Type} (p : Arlib.Computation.Charged Op Cell α) : ℕ :=
  p.cost Op.fairBit +
    Arlib.Computation.Op.all.foldl (fun total instruction =>
      total + p.cost (Op.word instruction)) 0

/-- Exact correctness of the candidate pretest on every promised input. The
same-rank and oracle conditions remain caller guards; feasibility is not one. -/
noncomputable def FeasibilityCorrect (solver : FeasibilityImplementation) : Prop :=
  ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n),
    FullGround M₁ M₂ → CommonRank r M₁ M₂ →
      ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
      (solver.run n r o₁ o₂).val = decide (0 < commonBaseCount M₁ M₂)

/-- A fixed polynomial bound, uniform over all oracle answers and inputs. The
bit side counts the same charged pretest as the correctness statement. -/
def FeasibilityBounded (solver : FeasibilityImplementation)
    (callConstant callDegree bitConstant bitDegree : ℕ) : Prop :=
  ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n),
    oracleCalls (solver.run n r o₁ o₂) ≤
      callConstant * (n + r + 1) ^ callDegree ∧
    otherSteps (solver.run n r o₁ o₂) ≤
      bitConstant * (n + r + 1) ^ bitDegree

/-- A cited solver package, if one is later constructed. Its existence is
currently unresolved; this structure does not manufacture an implementation. -/
structure FeasibilityContract where
  implementation : FeasibilityImplementation
  callConstant : ℕ
  callDegree : ℕ
  bitConstant : ℕ
  bitDegree : ℕ
  correct : FeasibilityCorrect implementation
  bounded : FeasibilityBounded implementation
    callConstant callDegree bitConstant bitDegree

end CountingMatroid.Model.Subroutines

end


