-- Prove2me | Definitions.Def_ShipConsol_OneWH_Supplement_TwoWarehouse
-- name    : ShipConsol_OneWH_Supplement_TwoWarehouse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:27:02.345223+00:00
-- url     : https://prove2.me/theorems/17d06036-a9ef-4458-9324-50b392c3ce6c
-- title:
--   §5, pp. 15–16 — symmetric two-warehouse Bellman model and six boundary regions
-- statement:
--   A symmetric fixed-cost instance has common nonnegative convex non-increasing cost F, deadline d≥1, independent arrival indicators of probabilities (α,β,α), and state (z_A,z_B,z_C). Each coordinate is either an active slack in {1,…,d} or absence ∞. A complete action ships or retains A and C and either retains B or assigns it once to W1 or W2. The two warehouse package costs are summed. Minimizing over these explicit assignments recovers
--
--   $$f(y_A,y_B,y_C)=\min\{F(\min(y_A,y_B))+F(y_C),\ F(y_A)+F(\min(y_B,y_C))\}.$$
--
--   Absent packages cost zero. Feasible actions satisfy deadlines and terminal shipment. The Bellman value is computed from these feasible complete actions. A shipment class is optimal when it has a feasible Bellman-optimal complete action as a completion; the other warehouse may also ship.
--
--   Six boundary functions depend on the other two slacks. They have the two nested A/C orderings, six optimal-completion implications, and the two B-absent identities. Their coverage condition selects a feasible optimal complete action at every state, with every shipment licensed by the boundary regions. If no region applies, this action holds every active type. This prevents all-zero witnesses. Ties can have distinct optimal completions assigning B to different warehouses; they never require B to ship twice. Absence is not compared with a large finite number. The default in extracting a finite slack is used only after excluding ∞.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, §§3,5.1, pp. 9–11,15–17; proof OA5–OA8 (PDF37–40)

import Mathlib
import Definitions.Def_ShipConsol_OneWH_Supplement_Control
import Definitions.Def_ShipConsol_OneWH_Supplement_Variable

namespace ShipConsol.OneWH.Supplement

/-- Coordinates 0,1,2 represent A,B,C; top means no pending orders. -/
abbrev ThreeSlacks := Fin 3 → WithTop ℕ
abbrev TwoAction := Bool × Fin 3 × Bool

structure SymmetricData where
  F : ℝ → ℝ
  d : ℕ
  α : ℝ
  β : ℝ

def SymmetricData.SourceData (D : SymmetricData) : Prop :=
  CostAssumptions D.F ∧ 1 ≤ D.d ∧
    D.α ∈ Set.Icc (0 : ℝ) 1 ∧ D.β ∈ Set.Icc (0 : ℝ) 1

def validSlack (d : ℕ) (z : WithTop ℕ) : Prop :=
  z = ⊤ ∨ ∃ n : ℕ, z = n ∧ 1 ≤ n ∧ n ≤ d

def validThree (d : ℕ) (s : ThreeSlacks) : Prop := ∀ i, validSlack d (s i)

def ships (a : TwoAction) (i : Fin 3) : Bool :=
  if i = 0 then a.1 else if i = 1 then a.2.1.val ≠ 0 else a.2.2

/-- B=0 holds, B=1 ships from W1, B=2 ships from W2. This prevents double assignment. -/
noncomputable def twoActions (t : ℕ) (s : ThreeSlacks) : Finset TwoAction := by
  classical
  exact Finset.univ.filter fun a => ∀ i,
    (s i = ⊤ → ships a i = false) ∧
    (s i ≠ ⊤ → (t = 1 ∨ s i = 1) → ships a i = true)

noncomputable def slackCost (F : ℝ → ℝ) (z : WithTop ℕ) : ℝ :=
  if z = ⊤ then 0 else F ((z.untopD (0 : ℕ) : ℕ) : ℝ)

noncomputable def twoCost (D : SymmetricData) (s : ThreeSlacks) (a : TwoAction) : ℝ :=
  slackCost D.F (min (if a.1 then s 0 else ⊤) (if a.2.1 = 1 then s 1 else ⊤)) +
  slackCost D.F (min (if a.2.2 then s 2 else ⊤) (if a.2.1 = 2 then s 1 else ⊤))

def ageSlack (z : WithTop ℕ) : WithTop ℕ := z.map (fun n => n - 1)

noncomputable def twoNext (D : SymmetricData) (s : ThreeSlacks) (a : TwoAction)
    (e : Fin 3 → Bool) : ThreeSlacks := fun i =>
  let r := if ships a i then ⊤ else ageSlack (s i)
  if e i then min r (D.d : WithTop ℕ) else r

noncomputable def twoWeight (D : SymmetricData) (e : Fin 3 → Bool) : ℝ :=
  ∏ i : Fin 3, let p := if i = 1 then D.β else D.α
              if e i then p else 1 - p

noncomputable def twoControl (D : SymmetricData) :
    ScenarioControl ThreeSlacks TwoAction (Fin 3 → Bool) where
  actions := twoActions
  cost := twoCost D
  next := twoNext D
  weight := twoWeight D

/-- Shipping an absent type is a vacuous action-class requirement. In particular,
AB coincides with A when B is absent, exactly as in the source's boundary identity. -/
def classA (s : ThreeSlacks) (a : TwoAction) : Prop := s 0 = ⊤ ∨ a.1 = true

def classC (s : ThreeSlacks) (a : TwoAction) : Prop := s 2 = ⊤ ∨ a.2.2 = true

def classAB (s : ThreeSlacks) (a : TwoAction) : Prop :=
  classA s a ∧ (s 1 = ⊤ ∨ a.2.1 = 1)

def classBC (s : ThreeSlacks) (a : TwoAction) : Prop :=
  classC s a ∧ (s 1 = ⊤ ∨ a.2.1 = 2)

noncomputable def classOptimal (D : SymmetricData) (t : ℕ) (s : ThreeSlacks)
    (C : ThreeSlacks → TwoAction → Prop) : Prop :=
  ∃ a, (twoControl D).BellmanOptimal t s a ∧ C s a

structure Boundaries where
  AAB : WithTop ℕ → WithTop ℕ → ℕ
  AA : WithTop ℕ → WithTop ℕ → ℕ
  CBC : WithTop ℕ → WithTop ℕ → ℕ
  CC : WithTop ℕ → WithTop ℕ → ℕ
  B1 : WithTop ℕ → WithTop ℕ → ℕ
  B2 : WithTop ℕ → WithTop ℕ → ℕ

def below (z : WithTop ℕ) (b : ℕ) : Prop := ∃ n : ℕ, z = n ∧ n ≤ b

/-- Every shipment made by a selected complete policy is licensed by the six
regions. Recommendations are separately required to have optimal completions;
conflicting B recommendations in a tie do not force B to ship twice. With no
applicable region, the selected policy must hold every active type. -/
def supportedAction (b : Boundaries) (s : ThreeSlacks) (a : TwoAction) : Prop :=
  (a.1 = true → below (s 0) (b.AA (s 1) (s 2)) ∨ below (s 1) (b.B1 (s 0) (s 2))) ∧
  (a.2.2 = true → below (s 2) (b.CC (s 0) (s 1)) ∨ below (s 1) (b.B2 (s 0) (s 2))) ∧
  (a.2.1 = 1 → below (s 0) (b.AAB (s 1) (s 2)) ∨ below (s 1) (b.B1 (s 0) (s 2))) ∧
  (a.2.1 = 2 → below (s 2) (b.CBC (s 0) (s 1)) ∨ below (s 1) (b.B2 (s 0) (s 2)))

def sixRegions (D : SymmetricData) (t : ℕ) (b : Boundaries) : Prop :=
  (∀ zB zC, validSlack D.d zB → validSlack D.d zC → b.AAB zB zC ≤ b.AA zB zC) ∧
  (∀ zA zB, validSlack D.d zA → validSlack D.d zB → b.CBC zA zB ≤ b.CC zA zB) ∧
  (∀ s, validThree D.d s →
    (below (s 0) (b.AAB (s 1) (s 2)) → classOptimal D t s classAB) ∧
    (below (s 0) (b.AA (s 1) (s 2)) → classOptimal D t s classA) ∧
    (below (s 1) (b.B1 (s 0) (s 2)) → classOptimal D t s classAB) ∧
    (below (s 1) (b.B2 (s 0) (s 2)) → classOptimal D t s classBC) ∧
    (below (s 2) (b.CBC (s 0) (s 1)) → classOptimal D t s classBC) ∧
    (below (s 2) (b.CC (s 0) (s 1)) → classOptimal D t s classC)) ∧
  (∀ zC, validSlack D.d zC → b.AAB ⊤ zC = b.AA ⊤ zC) ∧
  (∀ zA, validSlack D.d zA → b.CBC zA ⊤ = b.CC zA ⊤) ∧
  ∃ π : ThreeSlacks → TwoAction, ∀ s, validThree D.d s →
    (twoControl D).BellmanOptimal t s (π s) ∧ supportedAction b s (π s)

end ShipConsol.OneWH.Supplement


