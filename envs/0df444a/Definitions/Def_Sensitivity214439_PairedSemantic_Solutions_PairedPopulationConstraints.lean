-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
-- name    : Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:42.139226+00:00
-- url     : https://prove2.me/theorems/b78c8f43-2a7c-4c7a-baf9-45abbe93607c
-- title:
--   Four-tier population geometry and admissibility inequalities
-- statement:
--   A population is a function from four failure tiers to the natural numbers. Its prefix counts and weighted failure budgets are compared with a graded geometry: independent and marked caps, a tolerance tier, original prefix caps, a forest bound, high zero/one counts, and optional marker, power, and low-one data. Admissible is the conjunction of the corresponding edge, marker-copy, quadratic, forest, power-incidence, and low-one inequalities at each eligible tier. The bundle defines these arithmetic constraints and their finite decision instances. Its optional-data predicate imposes a condition exactly when that data is present.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/PairedPopulationConstraints.lean lines 11–134; SHA256 1f178788dc8ea7f18a6a9e69f66293d07dc2a4ec06522c0e03af06fc6d5356ad; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic

namespace SensitivityPairedPopulation
end SensitivityPairedPopulation



/-! Arithmetic interface between actual paired-row populations and the finite
population optimization.  The fields record bounds, not their semantic proofs;
`Admissible` is the conjunction that a semantic adapter must establish. -/
namespace SensitivityPairedPopulation

set_option autoImplicit false

abbrev Population := Fin 4 → ℕ

def prefixCount (n : Population) (q : Fin 4) : ℕ :=
  n 0 + (if 1 ≤ q.val then n 1 else 0) +
    (if 2 ≤ q.val then n 2 else 0) + (if 3 ≤ q.val then n 3 else 0)

def budget (n : Population) (q : Fin 4) : ℕ :=
  (if 1 ≤ q.val then n 1 else 0) +
    (if 2 ≤ q.val then 2 * n 2 else 0) + (if 3 ≤ q.val then 3 * n 3 else 0)



def minimumEdges (size alpha : ℕ) : ℕ :=
  alpha * (size / alpha).choose 2 + (size % alpha) * (size / alpha)

structure PowerData where
  heads : ℕ
  residual : ℕ
  macroGroups : ℕ
  alphaSum : Fin 3 → ℕ

structure LowOneData where
  populationPlusZero : ℕ
  zero : ℕ

structure GradedGeometry where
  alpha : ℕ
  beta : ℕ
  tolerance : Fin 4
  originalCap : Fin 4 → ℕ
  forestBound : ℕ
  highZero : ℕ
  highOne : ℕ
  markerResidual : Fin 7 → Option ℕ
  powers : Option PowerData
  lowOne : Option LowOneData

def markedConstraint (alpha size spent marks residual : ℕ) : Prop :=
  minimumEdges (size + marks) alpha ≤ spent + residual + marks.choose 2

def copyConstraint (beta size spent marks residual : ℕ) : Prop :=
  let covered := marks * size - residual
  let bestOutgoing := covered - (marks + 1) * (marks * beta)
  marks * bestOutgoing + minimumEdges (covered - bestOutgoing) (marks * beta) ≤ marks * spent

def markerQuadratic (alpha beta q size marks residual : ℕ) : Prop :=
  size ^ 2 + 2 * alpha * (marks * (size - (2 * q + 1) * beta) - residual) ≤
    alpha * ((2 * q + 1) * size)

def markerForest (alpha beta size marks residual : ℕ) : Prop :=
  if marks = 1 then 2 * size ≤ 3 * (alpha + beta) + 2 * residual
  else marks * size ≤ 3 * marks * beta + 2 * residual

def powerConstraint (data : PowerData) (size spent outgoing : ℕ) (order : Fin 3) : Prop :=
  let r := order.val + 1
  let appear := data.heads * size - outgoing - data.residual
  let copies := size * (appear / size).choose r + (appear % size) * (appear / size).choose order.val
  minimumEdges copies (data.alphaSum order) + data.heads.choose r * outgoing ≤
    data.heads.choose r * spent

def powerConstraints (data : PowerData) (size spent : ℕ) : Prop :=
  ∃ outgoing : Fin (spent + 1), ∀ order : Fin 3,
    order.val + 1 ≤ data.heads → powerConstraint data size spent outgoing.val order

def optional {A : Type} (data : Option A) (P : A → Prop) : Prop :=
  match data with
  | none => True
  | some value => P value

instance {A : Type} (data : Option A) (P : A → Prop) [∀ value, Decidable (P value)] :
    Decidable (optional data P) := by
  cases data <;> unfold optional <;> infer_instance

def Admissible (data : GradedGeometry) (n : Population) : Prop :=
  (∀ q : Fin 4, q ≤ data.tolerance → prefixCount n q ≤ data.originalCap q) ∧
  (∀ q : Fin 4, q ≤ data.tolerance →
    minimumEdges (prefixCount n q) data.alpha ≤ budget n q) ∧
  (1 ≤ data.tolerance.val →
    prefixCount n 1 + prefixCount n 0 ≤ data.forestBound ∧
    prefixCount n 1 + prefixCount n 0 + data.highOne + data.highZero ≤ 3 * data.alpha ∧
    ∀ m : Fin 7, optional (data.markerResidual m) (fun residual =>
      markerForest data.alpha data.beta (prefixCount n 1 + prefixCount n 0) (m.val + 1) residual)) ∧
  (∀ q : Fin 4, q ≤ data.tolerance → ∀ m : Fin 7,
    optional (data.markerResidual m) (fun residual =>
      markedConstraint data.alpha (prefixCount n q) (budget n q) (m.val + 1) residual ∧
      copyConstraint data.beta (prefixCount n q) (budget n q) (m.val + 1) residual ∧
      markerQuadratic data.alpha data.beta q.val (prefixCount n q) (m.val + 1) residual)) ∧
  optional data.powers (fun p =>
    ∀ q : Fin 4, q ≤ data.tolerance → powerConstraints p (prefixCount n q) (budget n q)) ∧
  optional data.lowOne (fun lo => 1 ≤ data.tolerance.val →
    prefixCount n 1 + prefixCount n 0 ≤ lo.populationPlusZero ∧ prefixCount n 0 ≤ lo.zero)

instance (alpha size spent marks residual : ℕ) :
    Decidable (markedConstraint alpha size spent marks residual) := by
  unfold markedConstraint
  infer_instance

instance (beta size spent marks residual : ℕ) :
    Decidable (copyConstraint beta size spent marks residual) := by
  unfold copyConstraint
  infer_instance

instance (alpha beta q size marks residual : ℕ) :
    Decidable (markerQuadratic alpha beta q size marks residual) := by
  unfold markerQuadratic
  infer_instance

instance (alpha beta size marks residual : ℕ) :
    Decidable (markerForest alpha beta size marks residual) := by
  unfold markerForest
  infer_instance

instance (data : PowerData) (size spent outgoing : ℕ) (order : Fin 3) :
    Decidable (powerConstraint data size spent outgoing order) := by
  unfold powerConstraint
  infer_instance

instance (data : PowerData) (size spent : ℕ) : Decidable (powerConstraints data size spent) := by
  unfold powerConstraints
  infer_instance

instance (data : GradedGeometry) (n : Population) : Decidable (Admissible data n) := by
  unfold Admissible
  infer_instance





end SensitivityPairedPopulation


