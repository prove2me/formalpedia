-- Prove2me | Definitions.Def_DynEdgeColorLLL_Main_Supplement_Repair
-- name    : DynEdgeColorLLL_Main_Supplement_Repair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:55.771202+00:00
-- url     : https://prove2.me/theorems/9f4138a8-9cd9-4ec1-8095-628945df0fc1
-- title:
--   Stored transcript repair, candidate sets and reconstruction
-- statement:
--   Fix finitely many variables, labelled clauses, a clause truth-table family, old variable sets and a batch of distinct incidence toggles. Use the published static process and one shared randomness table for the old and new instances. Let $r_x$ be the last stage resampling variable $x$, and define
--
--   $$\ell_C=\max(\{0\}\cup\{r_x:x\in\operatorname{vbl}(C)\}),\qquad
--   \ell_C^\star=\max(\{0\}\cup\{r_x^{\rm old}:x\in\operatorname{vbl}^{\rm old}(C)\cup\operatorname{vbl}^{\rm new}(C)\}).$$
--
--   The repair state contains stored selection sets, resampling bits, clause-falsification bits, counters, totals, last stages, the reported assignment, clause last stages, and candidates. Initialization updates the initial-assignment clause values and the affected counters. The stage recurrence performs the five steps in §3.3, retains uninspected entries, constructs $\overline{\mathcal C}_{r+1}$ by all three stated tests, and sets $\mathcal C_{r+1}$ to its closed neighbourhood in $H^\cup$. It runs stage one even if $\mathcal C_1$ is empty. Cleanup recomputes clause last stages only in the union of candidate sets.
--
--   Recovery means equality of stored entries to the published new static transcript; the invariants are predicates to be proved, not fields of a state. The assignment at a stage is read from the stored resampling bits. These mathematical process definitions carry no unit-cost operations: the RAM implementation must pay for every access, evaluation, sample and write, including the linked-list stage-access costs.
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §3.2–§3.4, Table 1 and five repair steps, printed pp. 10–16 (PDF pp. 12–18)

import Definitions.Def_DynEdgeColorLLL_Main_LLLTranscript

set_option autoImplicit false

namespace DynEdgeColorLLL.Main.Supplement

/-! Mathematical execution of §3.3 and the initialization/cleanup of §3.4.
These are mathematical process definitions, not unit-cost machine instructions.
All entries are stored values, initially copied from the old transcript. -/

variable {X : Type*} [Fintype X] [DecidableEq X] {Ω : X → Type*} {m : ℕ}

structure RepairState (X : Type*) (Ω : X → Type*) (m : ℕ) where
  selected : ℕ → Finset (Fin m)
  resampled : X → ℕ → Bool
  falsified : Fin m → ℕ → Bool
  counter : Fin m → ℕ → ℕ
  total : X → ℕ∞
  last : X → ℕ∞
  output : (x : X) → Ω x
  lastClause : Fin m → ℕ∞
  candidates : Finset (Fin m)
  previousBar : Finset (Fin m)

noncomputable def clauseLast (vbl : Fin m → Finset X) (last : X → ℕ∞)
    (C : Fin m) : ℕ∞ := (vbl C).sup last

noncomputable def starLast (f : TruthTables X Ω m) (old new : Fin m → Finset X)
    (τ : (x : X) → ℕ → Ω x) (C : Fin m) : ℕ∞ :=
  (old C ∪ new C).sup (rx f old τ)

noncomputable def storedAssign (τ : (x : X) → ℕ → Ω x)
    (st : RepairState X Ω m) (r : ℕ) : (x : X) → Ω x :=
  fun x => τ x (∑ j ∈ Finset.range r, if st.resampled x (j + 1) then 1 else 0)

noncomputable def bitTotal (bits : X → ℕ → Bool) (x : X) : ℕ∞ :=
  ⨆ t : ℕ, ((∑ j ∈ Finset.range t, if bits x (j + 1) then 1 else 0 : ℕ) : ℕ∞)

noncomputable def bitLast (bits : X → ℕ → Bool) (x : X) : ℕ∞ :=
  ⨆ (r : ℕ) (_ : 1 ≤ r ∧ bits x r = true), (r : ℕ∞)

open Classical in
noncomputable def closedNeighbors (H : SimpleGraph (Fin m))
    (A : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun C => ∃ D ∈ A, C = D ∨ H.Adj C D

open Classical in
/-- The actual initialization: evaluate changed clauses on σ₀, and recompute counters
in the closed neighbourhoods of touched clauses falsified before or after the batch. -/
noncomputable def initializeRepair (f : TruthTables X Ω m) (old : Fin m → Finset X)
    (B : Finset (Fin m × X)) (τ : (x : X) → ℕ → Ω x) : RepairState X Ω m :=
  let new := applyBatch old B
  let M := touched B
  let b : Fin m → Bool := fun C =>
    if C ∈ M then decide (f C (new C) (assignOf τ (fun _ => 0)))
    else decide (bC f old τ C 1)
  let A := closedNeighbors (unionDepGraph old new)
    (M.filter fun C => b C = true ∨ bC f old τ C 1)
  let cnt : Fin m → ℕ := fun C =>
    if C ∈ A then cntUnder f new (assignOf τ (fun _ => 0)) C else cntC f old τ C 1
  { selected := fun r => Finset.univ.filter (inI f old τ r)
    resampled := fun x r => decide (bx f old τ x r)
    falsified := fun C r => if r = 1 then b C else decide (bC f old τ C r)
    counter := fun C r => if r = 1 then cnt C else cntC f old τ C r
    total := sx f old τ
    last := rx f old τ
    output := finalAssign f old τ
    lastClause := clauseLast old (rx f old τ)
    candidates := Finset.univ.filter fun C =>
      b C ≠ decide (bC f old τ C 1) ∨ cnt C ≠ cntC f old τ C 1
    previousBar := ∅ }

open Classical in
/-- Precisely the five steps of §3.3. Uninspected stored entries are retained. -/
noncomputable def repairStage (f : TruthTables X Ω m) (old : Fin m → Finset X)
    (B : Finset (Fin m × X)) (τ : (x : X) → ℕ → Ω x) (r : ℕ)
    (st : RepairState X Ω m) : RepairState X Ω m :=
  let new := applyBatch old B
  let M := touched B
  let Iold := Finset.univ.filter (inI f old τ r)
  let I := (st.selected r \ st.candidates) ∪
    st.candidates.filter (fun C => st.falsified C r = true ∧ st.counter C r = 0)
  let inspected := symmDiff Iold I ∪ (M ∩ Iold ∩ I)
  let vars := inspected.biUnion (fun C => old C ∪ new C)
  let bits : X → ℕ → Bool := fun x j =>
    if j = r ∧ x ∈ vars then decide (∃ C ∈ I, x ∈ new C) else st.resampled x j
  let Z := vars.filter fun x => bits x r ≠ decide (bx f old τ x r)
  let last := fun x => if x ∈ Z then bitLast bits x else st.last x
  let total := fun x => if x ∈ Z then bitTotal bits x else st.total x
  let patched : RepairState X Ω m :=
    { st with
      selected := fun j => if j = r then I else st.selected j
      resampled := bits
      last := last
      total := total
      output := fun x => if x ∈ Z then τ x (total x).toNat else st.output x }
  let bar := Finset.univ.filter fun C =>
    (new C ∩ Z).Nonempty ∨
      (C ∈ st.candidates ∪ M ∧ (r : ℕ∞) ≤ starLast f old new τ C) ∨
      (C ∈ st.candidates ∧ 0 < st.counter C r)
  let next := closedNeighbors (unionDepGraph old new) bar
  let σ := storedAssign τ patched r
  { patched with
    falsified := fun C j =>
      if j = r + 1 ∧ C ∈ next then decide (f C (new C) σ) else st.falsified C j
    counter := fun C j =>
      if j = r + 1 ∧ C ∈ next then cntUnder f new σ C else st.counter C j
    candidates := next
    previousBar := bar }

/-- State before stage r. Stage one is always run, including when C₁ is empty.
The recurrence also defines the empty-stage extension after the first stop. -/
noncomputable def repairAt (f : TruthTables X Ω m) (old : Fin m → Finset X)
    (B : Finset (Fin m × X)) (τ : (x : X) → ℕ → Ω x) : ℕ → RepairState X Ω m
  | 0 => initializeRepair f old B τ
  | r + 1 => repairStage f old B τ (r + 1) (repairAt f old B τ r)

/-- Index t is zero-based: `repairAt ... t` is the state before stage t+1. -/
def StopsAfter (f : TruthTables X Ω m) (old : Fin m → Finset X)
    (B : Finset (Fin m × X)) (τ : (x : X) → ℕ → Ω x) (R : ℕ) : Prop :=
  1 ≤ R ∧ (repairAt f old B τ R).candidates = ∅ ∧
    ∀ t, 1 ≤ t → t < R → (repairAt f old B τ t).candidates ≠ ∅

/-- All three clauses of Lemma 5; assignments read the actually stored resampling bits. -/
def RepairInvariants (f : TruthTables X Ω m) (old : Fin m → Finset X)
    (B : Finset (Fin m × X)) (τ : (x : X) → ℕ → Ω x)
    (st : RepairState X Ω m) (r : ℕ) : Prop :=
  let new := applyBatch old B
  ((∀ j, 1 ≤ j → j < r → ∀ C, C ∈ st.selected j ↔ inI f new τ j C) ∧
    (∀ j, 1 ≤ j → j < r → ∀ x, st.resampled x j = true ↔ bx f new τ x j) ∧
    (∀ j, j < r → storedAssign τ st j = stageAssign f new τ j)) ∧
  (∀ C, IsDirty f old new τ C r → C ∈ st.candidates) ∧
  (∀ C j, 1 ≤ j → j ≤ r →
    (st.falsified C j = true ↔ bC f new τ C j) ∧ st.counter C j = cntC f new τ C j)

open Classical in
/-- Cleanup visits only clauses occurring in a candidate set before the stop. -/
noncomputable def cleanupRepair (f : TruthTables X Ω m) (old : Fin m → Finset X)
    (B : Finset (Fin m × X)) (τ : (x : X) → ℕ → Ω x) (R : ℕ) : RepairState X Ω m :=
  let st := repairAt f old B τ R
  let seen := (Finset.range (R + 1)).biUnion fun t => (repairAt f old B τ t).candidates
  { st with lastClause := fun C =>
      if C ∈ seen then clauseLast (applyBatch old B) st.last C else st.lastClause C }

/-- Equality of every stored transcript quantity, including totals, last stages and output. -/
def Reconstructs (f : TruthTables X Ω m) (new : Fin m → Finset X)
    (τ : (x : X) → ℕ → Ω x) (st : RepairState X Ω m) : Prop :=
  (∀ r, 1 ≤ r → ∀ C, C ∈ st.selected r ↔ inI f new τ r C) ∧
  (∀ r, 1 ≤ r → ∀ x, st.resampled x r = true ↔ bx f new τ x r) ∧
  (∀ r, 1 ≤ r → ∀ C,
    (st.falsified C r = true ↔ bC f new τ C r) ∧ st.counter C r = cntC f new τ C r) ∧
  (∀ j, storedAssign τ st j = stageAssign f new τ j) ∧
  st.total = sx f new τ ∧ st.last = rx f new τ ∧
  st.output = finalAssign f new τ ∧ st.lastClause = clauseLast new (rx f new τ)

/-- A finite correct old static transcript; not a termination hypothesis on the new repair. -/
def FiniteOld (f : TruthTables X Ω m) (old : Fin m → Finset X)
    (τ : (x : X) → ℕ → Ω x) : Prop :=
  ∃ t, ∀ C, ¬ f C (old C) (stageAssign f old τ t)

end DynEdgeColorLLL.Main.Supplement


