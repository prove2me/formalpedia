-- Prove2me | Definitions.Def_friedmann_cunningham
-- name    : friedmann_cunningham
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-02T05:10:49.975711+00:00
-- url     : https://prove2.me/theorems/b8a99c98-7d72-40ea-9060-531fb3768e15
-- title:
--   Explicit Cunningham lower-bound constructions
-- statement:
--   Explicit graph-derived Avis–Friedmann family: source-specific cyclic column ordering, prescribed exceptional initial action, collapsed absorbing MDP, exact parity graph with repeated-priority semantics, policy-to-basis map, and actual polytope realizability/AUSO/cube-walk predicates.
-- source:
--   Avis and Friedmann, Mathematical Programming2017, §§2–4; https://arxiv.org/abs/1305.3944

import Definitions.Def_friedmann_simplex
import Definitions.Def_friedmann_multiplicity
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-! Linear programs derived from Avis–Friedmann's Figure 7 via §4.2. Column numbers are
the cyclic ordering (1), rather than an arbitrary enumeration. Parameters n<3
are given total definitions but are excluded from every paper-level target.
The reward contribution of the aliases b₁=c₁=g₁ is retained explicitly; see
notes/cunningham-source-crosswalk.txt for the discrepancy with displayed §4.4.
-/
namespace FriedmannCunningham

open FriedmannSimplex
open scoped BigOperators
open Matrix

inductive Kind where
  | a | b | c | d | e
  deriving DecidableEq

structure Name where
  kind : Kind
  level : ℕ
  one : Bool
  deriving DecidableEq

def rows (n : ℕ) : ℕ := 5 * (n - 1)
def cols (n : ℕ) : ℕ := 10 * (n - 1)

def rowName (n : ℕ) (r : Fin (rows n)) : Kind × ℕ :=
  if r.val < n - 1 then (.a, r.val + 2)
  else if r.val < (n - 1) + (n - 2) then (.b, r.val - (n - 1) + 2)
  else if r.val < 2 * (n - 1) + (n - 2) then
    (.c, r.val - ((n - 1) + (n - 2)) + 2)
  else if r.val < 3 * (n - 1) + (n - 2) then
    (.d, r.val - (2 * (n - 1) + (n - 2)) + 2)
  else (.e, r.val - (3 * (n - 1) + (n - 2)) + 1)

def columnName (n : ℕ) (j : Fin (cols n)) : Name :=
  let k := j.val
  if k = 0 then ⟨.e, 1, true⟩
  else if k < 4 * n - 5 then
    let i := (k - 1) / 4 + 2
    match (k - 1) % 4 with
    | 0 => ⟨.d, i, false⟩
    | 1 => ⟨.e, i, true⟩
    | 2 => ⟨.b, i, true⟩
    | _ => ⟨.b, i, false⟩
  else if k < 6 * n - 7 then
    ⟨.c, (k - (4 * n - 5)) / 2 + 2, decide ((k - (4 * n - 5)) % 2 = 1)⟩
  else if k < 7 * n - 7 then ⟨.e, k - (6 * n - 7) + 1, false⟩
  else if k < 8 * n - 8 then ⟨.d, k - (7 * n - 7) + 2, true⟩
  else ⟨.a, n - (k - (8 * n - 8)) / 2, decide ((k - (8 * n - 8)) % 2 = 0)⟩

def columnRank (n : ℕ) (v : Name) : ℕ :=
  match v.kind, v.one with
  | .e, true => if v.level = 1 then 0 else 4 * (v.level - 2) + 2
  | .d, false => 4 * (v.level - 2) + 1
  | .b, true => 4 * (v.level - 2) + 3
  | .b, false => 4 * (v.level - 2) + 4
  | .c, false => 4 * n - 5 + 2 * (v.level - 2)
  | .c, true => 4 * n - 5 + 2 * (v.level - 2) + 1
  | .e, false => 6 * n - 7 + (v.level - 1)
  | .d, true => 7 * n - 7 + (v.level - 2)
  | .a, true => 8 * n - 8 + 2 * (n - v.level)
  | .a, false => 8 * n - 8 + 2 * (n - v.level) + 1

def indicator (v : Name) (kind : Kind) (i : ℕ) (one : Bool) : ℚ :=
  if v = ⟨kind, i, one⟩ then 1 else 0

def scale (n : ℕ) : ℚ := 2 * n + 1
def epsilon (n : ℕ) : ℚ := 1 / scale n ^ (2 * n + 2)
def rewardG (n i : ℕ) : ℚ := (-scale n) ^ (2 * i - 1)
def rewardH (n i : ℕ) : ℚ := (-scale n) ^ (2 * i)

/-- Coefficient of a named action in the displayed conservation equation. -/
def coefficient (n : ℕ) (r : Kind × ℕ) (v : Name) : ℚ :=
  let i := r.2
  let x := fun k l b => indicator v k l b
  let own := x r.1 i false + x r.1 i true
  let active := x .a i true + x .b i true + x .c i true +
    x .d i true + x .e i true
  match r.1 with
  | .a =>
      if i = 2 then own - epsilon n *
        (x .b 2 false + x .c 2 false + x .d 2 false + x .e 1 true)
      else own - x .a (i - 1) false - epsilon n *
        (x .a (i - 1) true + x .b (i - 1) true + x .c (i - 1) true +
          x .d (i - 1) true + x .e (i - 1) true)
  | .b => own - x .b (i + 1) false - x .d (i + 1) false
  | .c =>
      if i = n then own - ∑ j ∈ Finset.range (n + 1), x .e j false
      else own - x .c (i + 1) false
  | .d => own - (1 - epsilon n) / 2 * active
  | .e =>
      if i = 1 then own - (1 - epsilon n) *
        (x .b 2 false + x .c 2 false + x .d 2 false + x .e 1 true)
      else own - (1 - epsilon n) / 2 * active

def objectiveCoefficient (n : ℕ) (v : Name) : ℚ :=
  (match v.kind, v.one with
  | .a, true | .b, true | .c, true => rewardG n v.level + epsilon n * rewardH n v.level
  | .d, true | .e, true => epsilon n * rewardH n v.level
  | .e, false => 1
  | _, _ => 0) +
    (rewardG n 1 + epsilon n * rewardH n 1) *
      (indicator v .b 2 false + indicator v .c 2 false + indicator v .d 2 false)

def program (n : ℕ) : LP (rows n) (cols n) where
  A r j := coefficient n (rowName n r) (columnName n j)
  b _ := 1
  c j := objectiveCoefficient n (columnName n j)

def initialBit (r : Kind × ℕ) : Bool :=
  r.1 == .d || (r.1 == .e && r.2 == 1)

def initialBasis (n : ℕ) (hn : 3 ≤ n) : Basis (rows n) (cols n) :=
  fun r =>
    let name := rowName n r
    ⟨columnRank n ⟨name.1, name.2, initialBit name⟩ % cols n, by
      apply Nat.mod_lt
      unfold cols
      omega⟩

def initialState (n : ℕ) (hn : 3 ≤ n) : State (rows n) (cols n) where
  basis := initialBasis n hn
  last := ⟨0, by unfold cols; omega⟩

/-- The order is identity because column numbers already follow (1). -/
def order (n : ℕ) : Fin (cols n) ≃ Fin (cols n) := Equiv.refl _

def rowRank (n : ℕ) (r : Kind × ℕ) : ℕ :=
  match r.1 with
  | .a => r.2 - 2
  | .b => (n - 1) + (r.2 - 2)
  | .c => (n - 1) + (n - 2) + (r.2 - 2)
  | .d => 2 * (n - 1) + (n - 2) + (r.2 - 2)
  | .e => 3 * (n - 1) + (n - 2) + (r.2 - 1)

def actionColumn (n : ℕ) (hn : 3 ≤ n) (r : Fin (rows n)) (one : Bool) :
    Fin (cols n) :=
  let name := rowName n r
  ⟨columnRank n ⟨name.1, name.2, one⟩ % cols n, by
    apply Nat.mod_lt
    unfold cols
    omega⟩

abbrev Policy (n : ℕ) := Fin (rows n) → Bool

def policyBasis (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) : Basis (rows n) (cols n) :=
  fun r => actionColumn n hn r (σ r)

def initialPolicy (n : ℕ) : Policy n := fun r => initialBit (rowName n r)

/-- Transition probabilities between decision vertices after eliminating the
intermediate random vertices. The missing mass goes to the absorbing sink. -/
def transition (n : ℕ) (hn : 3 ≤ n) (r : Fin (rows n)) (one : Bool)
    (q : Fin (rows n)) : ℚ :=
  (if q = r then 1 else 0) - (program n).A q (actionColumn n hn r one)

def actionReward (n : ℕ) (hn : 3 ≤ n) (r : Fin (rows n)) (one : Bool) : ℚ :=
  (program n).c (actionColumn n hn r one)

noncomputable def policyValue (n : ℕ) (hn : 3 ≤ n) (σ : Policy n) :
    Fin (rows n) → ℚ :=
  (basisMatrix (program n) (policyBasis n hn σ))ᵀ⁻¹ *ᵥ
    (fun r => actionReward n hn r (σ r))

noncomputable def mdpImproving (n : ℕ) (hn : 3 ≤ n) (σ : Policy n)
    (r : Fin (rows n)) : Prop :=
  policyValue n hn σ r < actionReward n hn r (!σ r) +
    ∑ q : Fin (rows n), transition n hn r (!σ r) q * policyValue n hn σ q

structure MDPState (n : ℕ) where
  policy : Policy n
  last : Fin (cols n)

noncomputable def mdpStep (n : ℕ) (hn : 3 ≤ n) (s s' : MDPState n) : Prop :=
  ∃ r, mdpImproving n hn s.policy r ∧
    (∀ q, mdpImproving n hn s.policy q →
      cyclicDistance (order n) s.last (actionColumn n hn r (!s.policy r)) ≤
        cyclicDistance (order n) s.last (actionColumn n hn q (!s.policy q))) ∧
    s'.policy = Function.update s.policy r (!s.policy r) ∧
    s'.last = actionColumn n hn r (!s.policy r)

def initialMDPState (n : ℕ) (hn : 3 ≤ n) : MDPState n where
  policy := initialPolicy n
  last := ⟨0, by unfold cols; omega⟩

noncomputable def mdpRun (n : ℕ) (hn : 3 ≤ n) (s : ℕ → MDPState n) (T : ℕ) : Prop :=
  s 0 = initialMDPState n hn ∧
    (∀ t, t < T → mdpStep n hn (s t) (s (t + 1))) ∧
    ∀ r, ¬mdpImproving n hn (s T).policy r

def cubeAdjacent (n : ℕ) (σ τ : Policy n) : Prop :=
  ∃ r, σ r ≠ τ r ∧ ∀ q, q ≠ r → σ q = τ q

def inCubeFace (n : ℕ) (face : Fin (rows n) → Option Bool) (σ : Policy n) : Prop :=
  ∀ r b, face r = some b → σ r = b

noncomputable def cubeOrientation (n : ℕ) (hn : 3 ≤ n)
    (c : Fin (cols n) → ℚ) (σ τ : Policy n) : Prop :=
  cubeAdjacent n σ τ ∧
    objective { program n with c := c } (basicPoint (program n) (policyBasis n hn σ)) <
      objective { program n with c := c } (basicPoint (program n) (policyBasis n hn τ))

noncomputable def isAUSO (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ) : Prop :=
  (∀ σ τ, cubeAdjacent n σ τ →
    cubeOrientation n hn c σ τ ∨ cubeOrientation n hn c τ σ) ∧
  (∀ σ, ¬Relation.TransGen (cubeOrientation n hn c) σ σ) ∧
  ∀ face, ∃! σ, inCubeFace n face σ ∧
    ∀ τ, inCubeFace n face τ → ¬cubeOrientation n hn c σ τ

def isVertex {m k : ℕ} (P : LP m k) (x : Fin k → ℚ) : Prop :=
  feasible P x ∧ ∀ y z, feasible P y → feasible P z →
    (∀ j, x j = (y j + z j) / 2) → y = x ∧ z = x

def polytopeAdjacent {m k : ℕ} (P : LP m k) (x y : Fin k → ℚ) : Prop :=
  x ≠ y ∧ isVertex P x ∧ isVertex P y ∧
    ∀ z, feasible P z →
      (∀ j, x j = 0 → y j = 0 → z j = 0) →
      ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ j, z j = (1 - t) * x j + t * y j

/-- Realization uses actual extreme points and one-dimensional faces of the
feasible rational polytope, rather than a graph postulated as an extra field. -/
noncomputable def realizesCube (n : ℕ) (hn : 3 ≤ n) : Prop :=
  bounded (program n) ∧
  (∀ σ, isVertex (program n) (basicPoint (program n) (policyBasis n hn σ))) ∧
  (∀ x, isVertex (program n) x →
    ∃! σ, basicPoint (program n) (policyBasis n hn σ) = x) ∧
  ∀ σ τ, cubeAdjacent n σ τ ↔
    polytopeAdjacent (program n) (basicPoint (program n) (policyBasis n hn σ))
      (basicPoint (program n) (policyBasis n hn τ))

noncomputable def cubeStep (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ)
    (s s' : MDPState n) : Prop :=
  ∃ r, cubeOrientation n hn c s.policy (Function.update s.policy r (!s.policy r)) ∧
    (∀ q, cubeOrientation n hn c s.policy (Function.update s.policy q (!s.policy q)) →
      cyclicDistance (order n) s.last (actionColumn n hn r (!s.policy r)) ≤
        cyclicDistance (order n) s.last (actionColumn n hn q (!s.policy q))) ∧
    s'.policy = Function.update s.policy r (!s.policy r) ∧
    s'.last = actionColumn n hn r (!s.policy r)

noncomputable def cubeRun (n : ℕ) (hn : 3 ≤ n) (c : Fin (cols n) → ℚ)
    (s : ℕ → MDPState n) (T : ℕ) : Prop :=
  s 0 = initialMDPState n hn ∧
    (∀ t, t < T → cubeStep n hn c (s t) (s (t + 1))) ∧
    ∀ τ, ¬cubeOrientation n hn c (s T).policy τ

/- The parity-game companion uses the source's repeated priorities. -/

def vertices (n : ℕ) : ℕ := rows n + 3 * n + 2

def vertexCode (n : ℕ) (k : ℕ) : Fin (vertices n) :=
  ⟨k % vertices n, Nat.mod_lt _ (by unfold vertices; omega)⟩

def sinkVertex (n : ℕ) : Fin (vertices n) := vertexCode n (rows n + 3 * n + 1)
def sVertex (n : ℕ) : Fin (vertices n) := vertexCode n (rows n + 3 * n)
def fVertex (n i : ℕ) : Fin (vertices n) := vertexCode n (rows n + (i - 1))
def gVertex (n i : ℕ) : Fin (vertices n) := vertexCode n (rows n + n + (i - 1))
def hVertex (n i : ℕ) : Fin (vertices n) := vertexCode n (rows n + 2 * n + (i - 1))

def decisionVertex (n : ℕ) (k : Kind) (i : ℕ) : Fin (vertices n) :=
  if k = .a ∧ i = n + 1 then sinkVertex n
  else if (k = .b ∨ k = .c) ∧ i = 1 then gVertex n 1
  else vertexCode n (rowRank n (k, i))

def actionSource (n : ℕ) (j : Fin (cols n)) : Fin (vertices n) :=
  let v := columnName n j
  decisionVertex n v.kind v.level

def actionTarget (n : ℕ) (v : Name) : Fin (vertices n) :=
  match v.kind, v.one with
  | .a, true | .b, true | .c, true => gVertex n v.level
  | .a, false => decisionVertex n .a (v.level + 1)
  | .b, false | .d, false => decisionVertex n .b (v.level - 1)
  | .c, false => decisionVertex n .c (v.level - 1)
  | .d, true | .e, true => fVertex n v.level
  | .e, false => sVertex n

def gameSuccessors (n : ℕ) (v : Fin (vertices n)) : Finset (Fin (vertices n)) :=
  if hv : v.val < rows n then
    let r := rowName n ⟨v.val, hv⟩
    {actionTarget n ⟨r.1, r.2, false⟩, actionTarget n ⟨r.1, r.2, true⟩}
  else if v.val < rows n + n then
    let i := v.val - rows n + 1
    if i = 1 then {hVertex n i, decisionVertex n .e i}
    else {hVertex n i, decisionVertex n .d i, decisionVertex n .e i}
  else if v.val < rows n + 2 * n then
    {fVertex n (v.val - (rows n + n) + 1)}
  else if v.val < rows n + 3 * n then
    {decisionVertex n .a (v.val - (rows n + 2 * n) + 2)}
  else if v = sVertex n then {decisionVertex n .c n}
  else {sinkVertex n}

def gamePriority (n : ℕ) (v : Fin (vertices n)) : ℕ :=
  if hv : v.val < rows n then
    match (rowName n ⟨v.val, hv⟩).1 with
    | .a | .b | .c => 3
    | .d | .e => 5
  else if v.val < rows n + n then 6
  else if v.val < rows n + 2 * n then 2 * (v.val - (rows n + n) + 1) + 7
  else if v.val < rows n + 3 * n then 2 * (v.val - (rows n + 2 * n) + 1) + 8
  else if v = sVertex n then 8
  else 1

def parityGame (n : ℕ) : FriedmannParity.Game (Fin (vertices n)) where
  owner v := decide (rows n ≤ v.val)
  priority := gamePriority n
  edge v w := w ∈ gameSuccessors n v

def initialStrategy (n : ℕ) : Fin (vertices n) → Fin (vertices n) := fun v =>
  if hv : v.val < rows n then
    let r := rowName n ⟨v.val, hv⟩
    actionTarget n ⟨r.1, r.2, initialBit r⟩
  else v

structure ParityState (n : ℕ) where
  strategy : Fin (vertices n) → Fin (vertices n)
  last : Fin (cols n)

def initialParityState (n : ℕ) (hn : 3 ≤ n) : ParityState n where
  strategy := initialStrategy n
  last := ⟨0, by unfold cols; omega⟩

def parityStep (n : ℕ) (s s' : ParityState n) : Prop :=
  ∃ j : Fin (cols n),
    FriedmannMultiplicity.Improving (parityGame n) s.strategy
      (actionSource n j) (actionTarget n (columnName n j)) ∧
    (∀ k : Fin (cols n),
      FriedmannMultiplicity.Improving (parityGame n) s.strategy
        (actionSource n k) (actionTarget n (columnName n k)) →
      cyclicDistance (order n) s.last j ≤ cyclicDistance (order n) s.last k) ∧
    s'.strategy = Function.update s.strategy (actionSource n j)
      (actionTarget n (columnName n j)) ∧ s'.last = j

def parityRun (n : ℕ) (hn : 3 ≤ n) (s : ℕ → ParityState n) (T : ℕ) : Prop :=
  s 0 = initialParityState n hn ∧
    (∀ t, t ≤ T → FriedmannParity.Legal (parityGame n) false (s t).strategy) ∧
    (∀ t, t < T → parityStep n (s t) (s (t + 1))) ∧
    ¬FriedmannMultiplicity.Improvable (parityGame n) (s T).strategy

end FriedmannCunningham


