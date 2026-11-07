-- Prove2me | Definitions.Def_MetricMSO_CorrectAnswer
-- name    : MetricMSO_CorrectAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:16.774538+00:00
-- url     : https://prove2.me/theorems/24ea2d6e-9441-46c1-b800-4fe5984898bc
-- title:
--   The six tasks, solution sets, additive objectives and correct answers
-- statement:
--   The six tasks are: decide whether a satisfying assignment exists; compute a minimum-weight or maximum-weight satisfying assignment; count the satisfying assignments; count the minimum-weight or maximum-weight satisfying assignments.
--
--   The **solution set** is
--   $$\mathrm{Sol}_\varphi(G):=\Bigl\{(S_1,\dots,S_r)\in\prod_{i=1}^r2^{D_i(G)}:G\models\varphi(S_1,\dots,S_r)\Bigr\},$$
--   with $D_i(G)=V(G)$ for a vertex-set variable and $D_i(G)=E(G)$ for an edge-set variable. With integer weights $w_i:D_i(G)\to\mathbb Z$ the **objective** is
--   $$w(S_1,\dots,S_r):=\sum_{i=1}^r\sum_{a\in S_i}w_i(a).$$
--
--   A correct answer is: for deciding, the bit saying whether a solution exists; for optimization, the optimum value together with an assignment attaining it, or a report that no satisfying assignment exists; for counting, the number in binary, which is $0$ when no solution exists.
--
--   **Formalization Note** Several assignments may be optimal, so `CorrectAnswer` is a relation: any optimal assignment is correct, and the written value must be the true optimum. Numbers use the published `encodeNat` and `encodeInt`.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.7, Definitions 2.6, 2.7, pp.16–17 (PDF 18–19)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_MetricMSO_Sat

namespace MetricMSO

open ExponomialAssortment.FPTAS (encodeNat encodeInt)

/-- The six tasks of Theorem 1.1: decide whether a satisfying assignment exists (model checking is
the case without free variables), compute a minimum-weight or a maximum-weight satisfying
assignment, count the satisfying assignments, count the minimum-weight or the maximum-weight
satisfying assignments. -/
inductive Task : Type
  | decide
  | minimize
  | maximize
  | count
  | countMin
  | countMax
  deriving DecidableEq

/-- The index of a task, used in its binary code. -/
def Task.index : Task → ℕ
  | .decide => 0
  | .minimize => 1
  | .maximize => 2
  | .count => 3
  | .countMin => 4
  | .countMax => 5

/-- The tasks that take weights as part of their input. -/
def Task.weighted : Task → Bool
  | .decide => false
  | .count => false
  | _ => true

/-- **Weights** (Definition 2.6): a weight function `w_i : D_i(G) → ℤ` for each free set variable;
`wV i : V(G) → ℤ` for the vertex-set variable `X_{i+1}` and `wE i : E(G) → ℤ` for the edge-set
variable `Y_{i+1}` (only its values on edges are used). -/
structure Weights (I : Instance) (rV rE : ℕ) where
  wV : Fin rV → Fin I.n → ℤ
  wE : Fin rE → Sym2 (Fin I.n) → ℤ

/-- An assignment `(S₁, …, S_{rV}; T₁, …, T_{rE})` of the free set variables. -/
abbrev Assignment (I : Instance) (rV rE : ℕ) :=
  (Fin rV → Finset (Fin I.n)) × (Fin rE → Finset (Sym2 (Fin I.n)))

/-- The variable assignment in which the free vertex-set variables of levels `0, …, rV − 1` and the
free edge-set variables of levels `0, …, rE − 1` take the values of `A`. -/
def Assignment.toEnv {I : Instance} {rV rE : ℕ} (A : Assignment I rV rE) : Env I.n :=
  ⟨[], [], List.ofFn A.1, List.ofFn A.2⟩

/-- **The solution set `Sol_φ(G)`** (§2.7, p.16 (PDF 18)): "Solφ(G) := {(S1, . . . , Sr) ∈
∏_{i=1}^r 2^{Di(G)} : G |= φ(S1, . . . , Sr)}", with `D_i(G) = V(G)` for a vertex-set variable and
`D_i(G) = E(G)` for an edge-set variable. -/
def Sol (I : Instance) (φ : Formula) (rV rE : ℕ) : Set (Assignment I rV rE) :=
  {A | (∀ i, ∀ d ∈ A.2 i, d ∈ I.G.edgeSet) ∧ Sat I A.toEnv φ}

/-- **The additive objective** of Definition 2.6, p.17 (PDF 19):
`w(S1, …, Sr) := ∑_{i=1}^r ∑_{a∈Si} wi(a)`. -/
def weight {I : Instance} {rV rE : ℕ} (w : Weights I rV rE) (A : Assignment I rV rE) : ℤ :=
  ∑ i, ∑ a ∈ A.1 i, w.wV i a + ∑ i, ∑ d ∈ A.2 i, w.wE i d

/-- The minimum-weight satisfying assignments. -/
def MinSol (I : Instance) (φ : Formula) (rV rE : ℕ) (w : Weights I rV rE) :
    Set (Assignment I rV rE) :=
  {A | A ∈ Sol I φ rV rE ∧ ∀ B ∈ Sol I φ rV rE, weight w A ≤ weight w B}

/-- The maximum-weight satisfying assignments. -/
def MaxSol (I : Instance) (φ : Formula) (rV rE : ℕ) (w : Weights I rV rE) :
    Set (Assignment I rV rE) :=
  {A | A ∈ Sol I φ rV rE ∧ ∀ B ∈ Sol I φ rV rE, weight w B ≤ weight w A}

open Classical in
/-- Binary code of an assignment: for each vertex-set variable the `n` membership bits of the
vertices `0, …, n − 1`, then for each edge-set variable the `n²` membership bits of the pairs
`{a, b}` in the order `(a, b) ∈ Fin n × Fin n`. -/
noncomputable def encodeAssignment {I : Instance} {rV rE : ℕ} (A : Assignment I rV rE) :
    List Bool :=
  (List.ofFn fun i => List.ofFn fun a : Fin I.n => decide (a ∈ A.1 i)).flatten ++
  (List.ofFn fun i => (List.ofFn fun a : Fin I.n => List.ofFn fun b : Fin I.n =>
    decide (s(a, b) ∈ A.2 i)).flatten).flatten

open Classical in
/-- **Correct answers for each task** (Definitions 2.6 and 2.7, p.17 (PDF 19)).

* `decide`: `[true]` if a satisfying assignment exists, `[false]` otherwise.
* `minimize` (`maximize`): if there is no satisfying assignment, `[false]` ("report that no
  satisfying assignment exists"); otherwise `true` followed by the signed binary code of the optimum
  value and the code of a satisfying assignment attaining it ("We return the optimum value together
  with an assignment attaining it").
* `count`: `#φ(G) = |Sol_φ(G)|` in binary.
* `countMin` (`countMax`): the number of minimum-weight (maximum-weight) satisfying assignments in
  binary; this is `0` when no satisfying assignment exists ("In either case, we return zero when no
  satisfying assignment exists").

**Formalization Note** Several assignments may be optimal, so this is a relation: any optimal
assignment is a correct answer, and the value written must be the true optimum. Numbers are
written with the published self-delimiting binary codes `encodeNat`, `encodeInt`. -/
noncomputable def CorrectAnswer (task : Task) (I : Instance) (φ : Formula) (rV rE : ℕ)
    (w : Weights I rV rE) (out : List Bool) : Prop :=
  match task with
  | .decide => out = [decide (Sol I φ rV rE).Nonempty]
  | .minimize =>
      (Sol I φ rV rE = ∅ ∧ out = [false]) ∨
      ∃ A ∈ MinSol I φ rV rE w, out = true :: (encodeInt (weight w A) ++ encodeAssignment A)
  | .maximize =>
      (Sol I φ rV rE = ∅ ∧ out = [false]) ∨
      ∃ A ∈ MaxSol I φ rV rE w, out = true :: (encodeInt (weight w A) ++ encodeAssignment A)
  | .count => out = encodeNat (Sol I φ rV rE).ncard
  | .countMin => out = encodeNat (MinSol I φ rV rE w).ncard
  | .countMax => out = encodeNat (MaxSol I φ rV rE w).ncard

end MetricMSO


