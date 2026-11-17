-- Prove2me | Definitions.Def_FreeReplExchange_Supplement_BundleExchange
-- name    : FreeReplExchange_Supplement_BundleExchange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:32:54.49356+00:00
-- url     : https://prove2.me/theorems/8b3bc8c8-7a0f-4f9d-b72a-1d2a3a210e16
-- title:
--   MIC pairwise exchanges of nonempty bundles and their binary decision language
-- statement:
--   A **bundle exchange** atomically swaps two nonempty finite bundles between two distinct agents. Every offered good must belong to its giver initially, so onward sharing is forbidden. Executing a proposal set unions received goods into Boolean holdings; duplicate receipts count once. A proposal set is MIC when accepting every incident bundle exchange is a best response for each agent against every decision profile.
--
--   A finite accept-all schedule is valid when every round is MIC at the allocation reached by earlier rounds and every bundle respects a stated cardinality bound. The binary decision language records the agent and good counts, the Boolean initial allocation, exact rational ESC factors, and a threshold $T$; it accepts exactly when a valid MIC schedule with bundle size at most $5$ reaches at least $T$ filled slots.
--
--   This language is the decision form of the maximization problem in Theorem 7.
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), section 3.6, pp.26--28 (PDF pp.28--30), Theorem 7

import Mathlib
import Definitions.Def_FreeReplExchange_util
import Definitions.Def_KingTerrain_NPHard_Complexity
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- A pairwise atomic exchange of nonempty bundles, section 3.6, p. 26 (PDF p. 28). Agent `i` gives
`giveI` to `j`, and `j` gives `giveJ` to `i`; execution is atomic. -/
structure BundleExchange (A : Type*) (m : ℕ) where
  i : A
  j : A
  giveI : Finset (Fin m)
  giveJ : Finset (Fin m)
  deriving DecidableEq

/-- Bundle well-formedness: the agents are in the fixed normal order, both bundles are nonempty,
and every offered good belongs to its giver in the initial allocation.  Thus onward sharing is
excluded, section 3.6, p. 26 (PDF p. 28). -/
def BundleWellFormed {A : Type*} [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (p : BundleExchange A m) : Prop :=
  p.i < p.j ∧ p.giveI.Nonempty ∧ p.giveJ.Nonempty ∧
    (∀ r ∈ p.giveI, x0 p.i r = true) ∧ (∀ r ∈ p.giveJ, x0 p.j r = true)

open Classical in
/-- Execute a finite set of bundle exchanges atomically at allocation `x`.  Received goods are
unioned into Boolean holdings, so duplicate receipts count once. -/
noncomputable def execBundles {A : Type*} {m : ℕ} (x : A → Fin m → Bool)
    (S : Finset (BundleExchange A m)) : A → Fin m → Bool :=
  fun k r => x k r || decide (∃ p ∈ S,
    (k = p.j ∧ r ∈ p.giveI) ∨ (k = p.i ∧ r ∈ p.giveJ))

open Classical in
/-- The bundle allocation under a profile of accept/reject decisions: a bundle exchange executes
as a whole exactly when both participants accept it. -/
noncomputable def bundleOutcome {A : Type*} {m : ℕ} (x : A → Fin m → Bool)
    (S : Finset (BundleExchange A m)) (δ : A → BundleExchange A m → Bool) :
    A → Fin m → Bool :=
  execBundles x (S.filter fun p => δ p.i p && δ p.j p)

/-- Myopic incentive compatibility for a set of atomic bundle proposals: accepting every incident
proposal is a best response for each agent against every profile of the others' decisions, the
bundle analogue of equation (7), section 3.6, pp. 26--27 (PDF pp. 28--29). -/
def IsBundleMICSet {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (U : A → A → Fin m → ℝ) (x : A → Fin m → Bool)
    (S : Finset (BundleExchange A m)) : Prop :=
  ∀ (i : A) (δ : A → BundleExchange A m → Bool),
    util U i (bundleOutcome x S δ) ≤
      util U i (bundleOutcome x S (Function.update δ i fun _ => true))

/-- Validity of a finite accepting-path schedule of bundle proposal sets.  Every proposal uses only
initially owned goods, each bundle has cardinality at most `B`, and every round is MIC at the
allocation reached by the preceding accepting rounds. -/
def IsBundleSchedule {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (B : ℕ) :
    (A → Fin m → Bool) → List (Finset (BundleExchange A m)) → Prop
  | _, [] => True
  | x, S :: rest =>
      (∀ p ∈ S, BundleWellFormed x0 p ∧ p.giveI.card ≤ B ∧ p.giveJ.card ≤ B) ∧
        IsBundleMICSet U x S ∧ IsBundleSchedule x0 U B (execBundles x S) rest

/-- The terminal accepting-profile allocation of a finite bundle schedule. -/
noncomputable def runBundleSchedule {A : Type*} {m : ℕ} (x0 : A → Fin m → Bool) :
    List (Finset (BundleExchange A m)) → A → Fin m → Bool
  | [] => x0
  | S :: rest => runBundleSchedule (execBundles x0 S) rest

/-- A binary-encoded instance for the two restricted sharing-maximization decision problems of
Theorems 7 and 8. -/
structure SharingInstance where
  n : ℕ
  m : ℕ
  x0 : Fin n → Fin m → Bool
  beta : Fin n → Fin n → ℚ
  threshold : ℕ

/-- The ESC utility family determined by rational competition factors. -/
noncomputable def SharingInstance.U (I : SharingInstance) : Fin I.n → Fin I.n → Fin I.m → ℝ :=
  fun i j _ => if i = j then 1 else -(I.beta i j : ℝ)

/-- The real competition-factor family determined by a rational input table. -/
noncomputable def SharingInstance.betaReal (I : SharingInstance) : Fin I.n → Fin I.n → ℝ :=
  fun i j => (I.beta i j : ℝ)

/-- Length-faithful binary encoding of a sharing instance: dimensions, the Boolean initial-allocation
table, the exact rational competition table, and the filled-slot threshold. -/
def encodeSharingInstance (I : SharingInstance) : List Bool :=
  OptimalQueuingComplexity.Restless.encNat I.n ++
    OptimalQueuingComplexity.Restless.encNat I.m ++
    OptimalQueuingComplexity.Restless.encTable
      (fun row : Fin I.m → Bool =>
        OptimalQueuingComplexity.Restless.encTable (fun b => [b]) row) I.x0 ++
    OptimalQueuingComplexity.Restless.encTable
      (fun row : Fin I.n → ℚ =>
        OptimalQueuingComplexity.Restless.encTable
          OptimalQueuingComplexity.Restless.encRat row) I.beta ++
    OptimalQueuingComplexity.Restless.encNat I.threshold

/-- The restricted decision language underlying Theorem 7: an exact rational ESC instance is a yes
instance when some finite accepting-path MIC schedule of pairwise atomic bundle exchanges, every
bundle of size at most five and every offered good initially owned, reaches the input filled-slot
threshold. -/
def bundleSharingLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ I : SharingInstance, w = encodeSharingInstance I ∧
      0 < I.n ∧ 0 < I.m ∧ IsESC I.U I.betaReal ∧
      ∃ rounds : List (Finset (BundleExchange (Fin I.n) I.m)),
        IsBundleSchedule I.x0 I.U 5 I.x0 rounds ∧
          I.threshold ≤ filledCount (runBundleSchedule I.x0 rounds)}

end FreeReplExchange.Supplement


