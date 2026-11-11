-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_OracleRuns
-- name    : FiniteGroupTesting_LinearQuery_OracleRuns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:47.052377+00:00
-- url     : https://prove2.me/theorems/9b18eda4-ce17-492a-882f-be283daf0260
-- title:
--   Charged finite adaptive oracle runs
-- statement:
--   A finite run can return a value, execute a specified number of local instructions, query an ordered table entry and branch on its answer, or sample independently and uniformly from a nonempty finite interval and branch on the result. Each query is charged one oracle call and one time instruction; each uniform draw costs one time instruction. A completed execution records its decision, charged time and a ghost query transcript.
--
--   $$\operatorname{Resources}(P,Q,T)\iff\forall *,\ \forall r\text{ executing }P^*,\quad |\operatorname{transcript}(r)|\le Q\ \land\ \operatorname{time}(r)\le T.$$
--
--   Probabilities average independently at successive sample nodes. The run tree is denotational: it is never enumerated or stored by the tester. Local blocks below contain explicit finite array routines with conservative instruction charges. No correctness or resource property is an input field. The RAM and exact-uniform primitive are the stated reading of the paper's computation convention.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 13, 20–24, Definition 2.1 and §§3.2–3.5 computation model

import Definitions.Def_FiniteGroupTesting_LinearQuery_TableModel

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

attribute [local instance] Classical.propDecidable

/-- Finite adaptive run trees. A sample is exact uniform sampling, one RAM instruction.
`step` records charged local RAM instructions; queries cost both a query and a time step.
This is a semantics, not a claim that arbitrary run trees are efficiently constructible. -/
inductive OracleRun (n : ℕ) (α : Type)
  | done : α → OracleRun n α
  | step : ℕ → OracleRun n α → OracleRun n α
  | query : Fin n → Fin n → (Fin n → OracleRun n α) → OracleRun n α
  | sample : (k : ℕ) → (Fin (k + 1) → OracleRun n α) → OracleRun n α

namespace OracleRun

def bind {n : ℕ} {α β : Type} (p : OracleRun n α) (f : α → OracleRun n β) : OracleRun n β :=
  match p with
  | .done a => f a
  | .step c p => .step c (bind p f)
  | .query x y next => .query x y (fun z => bind (next z) f)
  | .sample k next => .sample k (fun z => bind (next z) f)

instance {n : ℕ} : Monad (OracleRun n) where
  pure := .done
  bind := bind

/-- Local instructions, including loop control; evaluated data are stored RAM words/arrays. -/
def charge {n : ℕ} (c : ℕ) : OracleRun n Unit := .step c (.done ())

def ask {n : ℕ} (x y : Fin n) : OracleRun n (Fin n) := .query x y .done

def draw {n : ℕ} (k : ℕ) : OracleRun n (Fin (k + 1)) := .sample k .done

/-- One path includes all local instructions and the actual ordered query transcript. -/
structure Outcome (n : ℕ) (α : Type) where
  value : α
  time : ℕ
  transcript : List ((Fin n × Fin n) × Fin n)

/-- Possible outcomes, with randomness adversarial for worst-case resource claims. -/
inductive Executes {n : ℕ} {α : Type} (op : Table n) : OracleRun n α → Outcome n α → Prop
  | done (a : α) : Executes op (.done a) ⟨a, 0, []⟩
  | step (c : ℕ) (p : OracleRun n α) (r : Outcome n α) :
      Executes op p r → Executes op (.step c p) ⟨r.value, c + r.time, r.transcript⟩
  | query (x y : Fin n) (next : Fin n → OracleRun n α) (r : Outcome n α) :
      Executes op (next (op x y)) r → Executes op (.query x y next)
        ⟨r.value, r.time + 1, (((x, y), op x y) :: r.transcript)⟩
  | sample (k : ℕ) (next : Fin (k + 1) → OracleRun n α) (z : Fin (k + 1))
      (r : Outcome n α) : Executes op (next z) r →
        Executes op (.sample k next) ⟨r.value, r.time + 1, r.transcript⟩

/-- Exact finite probability, with independent choices at successive sample nodes. -/
noncomputable def probability {n : ℕ} {α : Type} (op : Table n) (event : α → Prop) :
    OracleRun n α → ℝ
  | .done a => if event a then 1 else 0
  | .step _ p => probability op event p
  | .query x y next => probability op event (next (op x y))
  | .sample k next => (∑ z : Fin (k + 1), probability op event (next z)) / (k + 1 : ℝ)

/-- No resource bound is a field of a program or of its output. -/
def ResourceBound {n : ℕ} {α : Type} (p : OracleRun n α) (queries time : ℝ) : Prop :=
  ∀ (op : Table n) (r : Outcome n α), Executes op p r →
    (r.transcript.length : ℝ) ≤ queries ∧ (r.time : ℝ) ≤ time

end OracleRun
end FiniteGroupTesting.LinearQuery


