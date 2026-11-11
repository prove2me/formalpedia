-- Prove2me | Definitions.Def_JainCRERepetition_Cubic_extraction
-- name    : JainCRERepetition_Cubic_extraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:44.508944+00:00
-- url     : https://prove2.me/theorems/89afdfed-857a-4d3c-a348-b811004ac876
-- title:
--   Definition 3.3 and Procedure 1 — coordinate targets with designated answer readers
-- statement:
--   A coordinate target has arbitrary finite Alice and Bob output spaces, a copied-input family, fixed designated answer readers, and two comparison operators. Comparison validity and divergence finiteness are separate predicates. Consistency means that its posterior is the actual unchecked-coordinate question law and that reading the designated answers reproduces the corresponding conditional question/answer law.
--
--   $$q_i(x,y)\Pr[\mathrm{read}_A=a,\mathrm{read}_B=b\mid x,y]=Q(X_i=x,Y_i=y,A_i=a,B_i=b).$$
--
--   The sum of the two local charges is computed from this data. Neither consistency nor either budget is included in the underlying data record. The extraction statement is allowed to use any consistent target with these readout laws, a generalization that includes every full coordinate view of Definition 3.4. Preparation resources and channels are finite and fixed before the fresh questions arrive.
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 23, Definition 3.3; p. 32, Procedure 1; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_repeated

open scoped BigOperators
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

/-- Input data for one coordinate preparation problem, including the original answer readers.
Consistency, comparison validity, finite divergences and the budgets are separate propositions. -/
structure TargetBranch (X Y A B : Type) [Fintype X] [Fintype Y] where
  DA : Type
  DB : Type
  [fa : Fintype DA] [fb : Fintype DB]
  [da : DecidableEq DA] [db : DecidableEq DB]
  family : CopiedFamily X Y DA DB
  readA : DA → A
  readB : DB → B
  comparisonA : Op (AliceIndex X Y DA)
  comparisonB : Op (AliceIndex Y X DB)

attribute [instance] TargetBranch.fa TargetBranch.fb TargetBranch.da TargetBranch.db

section Extraction
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable {n : ℕ} {G : QuantumParallelRepetition.Game X Y A B}
variable (S : QuantumParallelRepetition.Strategy (G.repeat n)) (C : Finset (Fin n))

def branchS (F : TargetBranch X Y A B) : ℝ :=
  bAlice F.family F.comparisonA + bBob F.family F.comparisonB

def branchesConsistent (F : Fin n → TargetBranch X Y A B) : Prop :=
  ∀ i ∈ unchecked C,
    (F i).family.prior = priorLaw G ∧
    (F i).family.posterior.p = coordinateLaw S C i ∧
    ∀ x y a b,
      (F i).family.posterior.p (x,y) *
        (∑ ab, if (F i).readA ab.1 = a ∧ (F i).readB ab.2 = b
          then Complex.normSq ((F i).family.vector x y ab) else 0) =
      ∑ z, if z.1.1 i = x ∧ z.1.2 i = y ∧ z.2.1 i = a ∧ z.2.2 i = b
        then posteriorWeight S C z else 0

def branchesValid (F : Fin n → TargetBranch X Y A B) : Prop :=
  ∀ i ∈ unchecked C,
    IsComparison (F i).family.prior (F i).comparisonA ∧
    IsComparison (F i).family.flip.prior (F i).comparisonB ∧
    FiniteD (aliceTarget (F i).family) (F i).comparisonA ∧
    FiniteD (aliceTarget (F i).family.flip) (F i).comparisonB

end Extraction
end JainCRERepetition.Cubic


