-- Prove2me | Definitions.Def_PandoraOrder_Tree_Contracts
-- name    : PandoraOrder_Tree_Contracts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:01:04.609749+00:00
-- url     : https://prove2.me/theorems/72b77b77-66a1-475a-8ca9-51ce6c81638e
-- title:
--   Semantic threshold specifications and full algorithmic optimality contracts
-- statement:
--   Semantic line annotations attach the least-root generalized threshold to every suffix. Semantic tree annotations recursively merge annotated child lists and prefix the current vertex with its semantic threshold. This specification is separate from the arithmetic program; it does not assert its own efficiency or optimality. The semantic union similarly merges independently annotated lines.
--
--   The optimality predicate requires admissibility and domination of every admissible history-based behavioral policy in actual expected payoff. It also states a representation conclusion for every independent private seed on an arbitrary probability space: measurable choices at each history and almost-sure legal policies induce an integrable payoff and an admissible behavioral policy with exactly the same expectation. Combined with the behavioral comparison, this includes correlated private randomness across decisions. Policies may be completed by stopping on impossible histories.
--
--   The algorithm contract requires a successful computation, exact agreement with the semantic annotation specification, and uniform polynomial bounds on both preprocessing counters. The returned labels must form a legal permutation of the input boxes, equal the reward-independent greedy order, and contain every realized search path as a prefix. At every nonnegative incumbent the actual threshold policy must be optimal. For every nonnegative realized reward vector, costed execution must agree with the mathematical rollout and the combined preprocessing-and-execution time and storage must satisfy the same polynomial bound.
--
--   The bound has the form $C(n+\sum_b s_b+1)^d$. Each theorem quantifies $C,d$ before all input instances. This does not assume success, bounded cost, value correctness or optimality. The zero-incumbent case is exactly the original search problem. The opening-value supremum, used by Claim 2, separately requires opening the first box; it can be negative.
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, Claims 2–3 and Theorems 5–7, pp. 8–11; Algorithm 2, p. 12; Appendix C, pp. 22–23; https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_Search

namespace PandoraOrder.Tree

noncomputable def pureMerge {n : ℕ} : ℕ → Annotated n → Annotated n → Annotated n
  | 0, _, _ => []
  | t + 1, A, B => match A, B with
      | [], _ => B
      | _, [] => A
      | a :: as, b :: bs =>
          if b.2 < a.2 ∨ (a.2 = b.2 ∧ a.1.val ≤ b.1.val)
          then a :: pureMerge t as B else b :: pureMerge t A bs

/-- Semantic Algorithm 2 specification; no computational claim is hidden here.
Recursion depth n suffices for a tree on n vertices, a fact required of the program. -/
noncomputable def semanticSubtree {n : ℕ} (I : Instance n)
    (T : HarelTarjan.Compressed.RootedTree (Fin n)) : ℕ → Fin n → Annotated n
  | 0, _ => []
  | t + 1, b =>
      let cs := (List.finRange n).filter (fun c => c ≠ T.root ∧ T.parent c = b)
      let merged := cs.foldl (fun A c =>
        let B := semanticSubtree I T t c
        pureMerge (A.length + B.length) A B) []
      (b, threshold I (b :: merged.map Prod.fst)) :: merged

noncomputable def semanticLine {n : ℕ} (I : Instance n) : List (Fin n) → Annotated n
  | [] => []
  | b :: L => (b, threshold I (b :: L)) :: semanticLine I L

noncomputable def semanticUnion {n : ℕ} (I : Instance n)
    (Ls : List (List (Fin n))) : Annotated n :=
  Ls.foldl (fun A L =>
    let B := semanticLine I L
    pureMerge (A.length + B.length) A B) []

/-- Concrete payoff from a policy which must open the next box first. -/
noncomputable def openingValue {n : ℕ} (I : Instance n) (b : Fin n)
    (L : List (Fin n)) (x : ℝ) : ℝ :=
  sSup {v | ∃ π : Policy n, Admissible (lineConstraint (b :: L)) π ∧
    (π []).prob (some b) = 1 ∧ value I π x = v}

noncomputable def outcomeWeight {n : ℕ} (I : Instance n)
    (ω : (b : Fin n) → Fin (I.size b)) : ℝ :=
  ∏ b : Fin n, (I.law b).prob (ω b)

/-- Optimality against every history-dependent behavioral policy. Arbitrarily
correlated private random seeds are included through the explicit representation
clause: they need not be resampled independently at each decision. -/
def Optimal {n : ℕ} (I : Instance n) (F : Constraint n) (x : ℝ)
    (πstar : Policy n) : Prop :=
  Admissible F πstar ∧
  (∀ π : Policy n, Admissible F π → value I π x ≤ value I πstar x) ∧
  (∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : @MeasureTheory.Measure Ω m),
    @MeasureTheory.IsProbabilityMeasure Ω m μ →
    ∀ choose : Ω → History n → Option (Fin n),
      (∀ h a, @MeasurableSet Ω m {ω | choose ω h = a}) →
      (∀ᵐ ω ∂μ, Admissible F (fun h => pureAction (choose ω h))) →
      MeasureTheory.Integrable (fun ω => value I (fun h => pureAction (choose ω h)) x) μ ∧
      ∃ π : Policy n, Admissible F π ∧
        value I π x = ∫ ω, value I (fun h => pureAction (choose ω h)) x ∂μ)

/-- The returned annotations are a full legal linearization. The rollout on every
nonnegative reward vector is its prefix, so only stopping adapts to the rewards. -/
def FixedOrder {n : ℕ} (F : Constraint n) (A : Annotated n) (boxes : List (Fin n)) : Prop :=
  (A.map Prod.fst).Perm boxes ∧
  (A.map Prod.fst).Nodup ∧
  Legal F (A.map (fun bz => (bz.1, (0 : ℝ)))) ∧
  greedyOrder F (annotation A) n [] = A.map Prod.fst ∧
  ∀ rewards : Fin n → ℝ, (∀ b, 0 ≤ rewards b) → ∀ x : ℝ, 0 ≤ x →
    rollout F (annotation A) rewards n [] x <+: A.map Prod.fst

/-- A successful executable preparation, with bounds for preprocessing plus every
possible execution. Constants are quantified outside instances in the theorem items. -/
def AlgorithmContract {n : ℕ} (I : Instance n) (F : Constraint n)
    (available : List (Fin n) → Fin n → Calc Bool)
    (program : Calc (Annotated n)) (spec : Annotated n) (boxes : List (Fin n))
    (C d : ℕ) : Prop :=
  ∃ A meter, program {} = some (A, meter) ∧ A = spec ∧
    meter.time ≤ C * (inputSize I + 1) ^ d ∧
    meter.cells ≤ C * (inputSize I + 1) ^ d ∧
    FixedOrder F A boxes ∧
    (∀ x : ℝ, 0 ≤ x → Optimal I F x (thresholdPolicy F (annotation A) x)) ∧
    ∀ rewards : Fin n → ℝ, (∀ b, 0 ≤ rewards b) → ∀ x : ℝ, 0 ≤ x →
      ∃ opened finalMeter,
        runProgram available A rewards n [] x meter = some (opened, finalMeter) ∧
        opened = rollout F (annotation A) rewards n [] x ∧
        finalMeter.time ≤ C * (inputSize I + 1) ^ d ∧
        finalMeter.cells ≤ C * (inputSize I + 1) ^ d

end PandoraOrder.Tree


