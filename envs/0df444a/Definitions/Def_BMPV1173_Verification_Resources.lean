-- Prove2me | Definitions.Def_BMPV1173_Verification_Resources
-- name    : BMPV1173_Verification_Resources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:13.264037+00:00
-- url     : https://prove2.me/theorems/4e3a5ae7-6d76-4c0f-a671-9ffaf6aa6d62
-- title:
--   Born probabilities, stopping budgets and clean coherent resource tasks
-- statement:
--   Defines finite quantum checkpoint programs whose partial observations retain the unobserved quantum state. The joint Born probability of a permitted answer and completion within a query budget is computed recursively with unnormalized projections, so zero-probability branches require no division. An Option address supplies a fixed-zero dummy query and permits empty-input zero-query programs. The structural query cap only defines the unrestricted output law; it is not information supplied to search. Fixed-count function/relation tasks and clean coherent maps retain actual counted XOR circuits, input-independent operations, and uniform norm error. Allowance validity specifies actual unfinished/correct answers and probability-one completion within the allowance. The older full-register-measurement wrappers remain explicitly restricted compatibility interfaces; source search milestones use the persistent-state model. No correctness or cost guarantee is a field of an algorithm.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §2.2 and Remark 2.8, printed pp.14–16 = PDF pp.14–16.

import Definitions.Def_BMPV1173_Verification_Preprocessing
import Definitions.Def_BMPV1173_Verification_QueryComplexity
import Definitions.Def_QAlgorithms_Defs_AdaptiveQuery

/-! Operational resource interfaces for §2.2. They use Born probabilities and
counted XOR calls, including measurement-dependent stopping. No success or resource
claim is a field of an algorithm. -/
namespace BMPV1173.Verification

open scoped BigOperators
noncomputable section

/-- A measured functional task. Every input in D uses the SAME circuit. -/
def HasFunction {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (D : Set (ι → Bool)) (f : (ι → Bool) → β) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ι Bool (Fin w) T)
    (out : (ι × Bool) × Fin w → β),
    ∀ x ∈ D, 1-ε ≤ A.outputProb (QAlgorithms.xorOracle x) out (f x)

/-- A measured relation, for approximate counting where many outputs are valid. -/
def HasRelation {ι β : Type} [Fintype ι] [DecidableEq ι]
    (D : Set (ι → Bool)) (R : (ι → Bool) → β → Prop) (ε : ℝ) (T : ℕ) : Prop := by
  classical
  exact ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ι Bool (Fin w) T)
    (out : (ι × Bool) × Fin w → β),
    ∀ x ∈ D, 1-ε ≤ QAlgorithms.probEvent (A.finalState (QAlgorithms.xorOracle x))
      (fun z => R x (out z))

/-- Apply the interleaved unitaries and counted oracle calls to an arbitrary state.
The stored start vector is unused here; the U fields are still input independent. -/
def applyCircuit {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    {T : ℕ} (A : QAlgorithms.QueryAlg ι Bool W T) (x : ι → Bool)
    (ψ : EuclideanSpace ℂ ((ι × Bool) × W)) : EuclideanSpace ℂ ((ι × Bool) × W) :=
  let states : Fin (T+1) → EuclideanSpace ℂ ((ι × Bool) × W) :=
    Fin.induction (QAlgorithms.act (A.U 0 : Matrix _ _ ℂ) ψ)
      (fun i v => QAlgorithms.act (A.U i.succ : Matrix _ _ ℂ)
        (QAlgorithms.act (Matrix.kronecker (QAlgorithms.xorOracle x) (1 : Matrix W W ℂ)) v))
  states (Fin.last T)

/-- A checkpoint program keeps its quantum register between observations.
`observe` partitions the computational basis; only this outcome is measured.
Ancillas and input-independent unitaries allow arbitrary finite measurements. -/
inductive StoppingProgram (ι W β : Type) [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] where
  | halt (out : ((Option ι × Bool) × W) → β)
  | round (T : ℕ) (A : QAlgorithms.QueryAlg (Option ι) Bool W T)
      (m : ℕ) (observe : ((Option ι × Bool) × W) → Fin m)
      (next : Fin m → StoppingProgram ι W β)

/-- Unnormalized projection onto one observed outcome. Keeping the norm
retains the branch probability without dividing by a possibly zero probability. -/
def projectOutcome {Z : Type} [Fintype Z] {m : ℕ}
    (observe : Z → Fin m) (h : Fin m) (ψ : EuclideanSpace ℂ Z) : EuclideanSpace ℂ Z :=
  WithLp.toLp 2 (fun z => if observe z = h then ψ z else 0)

/-- Born probability of a correct output and completion within the remaining
budget. Recursion retains the projected quantum state in each branch. -/
def StoppingProgram.boundedProb {ι W β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (x : ι → Bool) (P : β → Prop) :
    StoppingProgram ι W β → EuclideanSpace ℂ ((Option ι × Bool) × W) → ℝ → ℝ := by
  classical
  exact fun A => match A with
  | .halt out => fun ψ b => if 0 ≤ b then ∑ z, if P (out z) then ‖ψ z‖^2 else 0 else 0
  | .round T U m observe next => fun ψ b =>
      ∑ h : Fin m, (next h).boundedProb x P
        (projectOutcome observe h (applyCircuit U (fun i => i.elim false x) ψ)) (b-T)

/-- A finite structural cap used only to define the unrestricted output law;
it is never supplied to the search algorithm as a cost bound. -/
def StoppingProgram.queryCap {ι W β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] : StoppingProgram ι W β → ℕ
  | .halt _ => 0
  | .round T _ _ _ next => T + Finset.univ.sup (fun h => (next h).queryCap)

/-- A finite quantum test with persistent state and measured stopping history.
The dummy address `none` answers zero, allowing query-free/empty-domain tests;
for a nonempty entry oracle it is simulated in one query with a |+> target. -/
structure StoppingQueryAlg (ι β : Type) [Fintype ι] [DecidableEq ι] where
  w : ℕ
  start : EuclideanSpace ℂ ((Option ι × Bool) × Fin w)
  start_unit : ‖start‖ = 1
  program : StoppingProgram ι (Fin w) β

/-- Probability of output in P AND completion within b actual oracle calls. -/
def boundedStoppingProb {ι β : Type} [Fintype ι] [DecidableEq ι]
    (A : StoppingQueryAlg ι β) (x : ι → Bool) (P : β → Prop) (b : ℝ) : ℝ :=
  A.program.boundedProb x P A.start b

def StoppingQueryAlg.outProb {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (A : StoppingQueryAlg ι β) (x : ι → Bool) (a : β) : ℝ :=
  boundedStoppingProb A x (fun ans => ans = a) A.program.queryCap

/-- The query address and scratch are reset; σ contains the data registers. -/
def embedData {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (q0 : ι) (w : ℕ) (ψ : EuclideanSpace ℂ σ) :
    EuclideanSpace ℂ ((ι × Bool) × (σ × Fin (w+1))) :=
  ∑ s, ψ s • QAlgorithms.ket ((q0,false),(s,0))

/-- A clean coherent map, uniformly on all superpositions of admissible labels.
The before/after vectors specify the actual operation; the definition does not
assert that any low-query realization exists. -/
def HasCoherentMap {ι σ γ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] [Fintype γ] [DecidableEq γ]
    (q0 : ι) (D : Set (ι → Bool)) (valid : (ι → Bool) → γ → Prop)
    (before after : (ι → Bool) → γ → EuclideanSpace ℂ σ) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ι Bool (σ × Fin (w+1)) T),
    ∀ x ∈ D, ∀ amp : γ → ℂ, (∑ a, ‖amp a‖^2) = 1 →
      (∀ a, amp a ≠ 0 → valid x a) →
      ‖applyCircuit A x (embedData q0 w (∑ a, amp a • before x a)) -
        embedData q0 w (∑ a, amp a • after x a)‖ ≤ ε

def SearchAnswer {m : ℕ} (f : Fin m → Bool) (ans : Option (Fin m)) : Prop :=
  match ans with
  | none => ∀ j, f j = false
  | some j => f j = true

/-- The allowance protocol at one unknown input. Thresholds are semantic values,
not information supplied to the search. Costs and errors refer to actual runs. -/
def StoppingAllowanceValidAt {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (test : Fin m → ℕ → StoppingQueryAlg ι (Option Bool))
    (x : ι → Bool) (f : Fin m → Bool) (τ : Fin m → ℕ)
    (ε H : ℝ) (maxAllowance : ℕ) : Prop :=
  ∀ j u, 1 ≤ u → u ≤ maxAllowance →
    boundedStoppingProb (test j u) x (fun _ => True) (H*u) = 1 ∧
    1-ε ≤ boundedStoppingProb (test j u) x
      (fun ans => ans = if u < τ j then none else some (f j)) (H*u)

/-! Restricted full-register-measurement interfaces retained for existing clients.
The source search milestones use the persistent-state interfaces above. -/
/-- Probability of a correct output AND completion within a budget, not expected time. -/
def boundedOutputProb {ι β : Type} [Fintype ι] [DecidableEq ι]
    (A : QAlgorithms.AdaptiveQueryAlg ι β) (x : ι → Bool) (P : β → Prop) (b : ℝ) : ℝ := by
  classical
  exact match A with
  | .halt a => if P a ∧ 0 ≤ b then 1 else 0
  | .round T _ U next => ∑ z, QAlgorithms.prob (U.finalState (QAlgorithms.xorOracle x)) z *
      boundedOutputProb (next z) x P (b-T)


/-- The allowance protocol at one unknown input. Thresholds are semantic values,
not information supplied to the search. Costs and errors refer to actual runs. -/
def AllowanceValidAt {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (test : Fin m → ℕ → QAlgorithms.AdaptiveQueryAlg ι (Option Bool))
    (x : ι → Bool) (f : Fin m → Bool) (τ : Fin m → ℕ)
    (ε H : ℝ) (maxAllowance : ℕ) : Prop :=
  ∀ j u, 1 ≤ u → u ≤ maxAllowance →
    ((test j u).maxQueries x : ℝ) ≤ H*u ∧
    1-ε ≤ boundedOutputProb (test j u) x
      (fun ans => ans = if u < τ j then none else some (f j)) (H*u)

end
end BMPV1173.Verification


