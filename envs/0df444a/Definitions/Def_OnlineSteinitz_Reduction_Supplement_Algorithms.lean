-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Supplement_Algorithms
-- name    : OnlineSteinitz_Reduction_Supplement_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:12:52.751236+00:00
-- url     : https://prove2.me/theorems/5a55c5b8-9735-4318-b14c-aef7b968b7b0
-- title:
--   Causal online ordering rules and promised inputs
-- statement:
--   An online rule knows the horizon and dimension and, on each arrival, reads a private tape, the previous vector/placement history, and the current real Euclidean vector. It returns a slot immediately. Execution appends this pair and never changes an earlier pair. A legal input has unit-ball vectors and total zero. Validity means that on every legal input and every tape all slots are below the horizon and distinct; since there are exactly $T$ placements this is a permutation. The rule has no access to the final total or future vectors.
--
--   A deterministic rule uses a singleton tape. A randomized rule may use any probability space, with measurable decisions on each fixed history and vector. The separate adaptive execution gives the adversary precisely the earlier placement history. Its legal-run predicate checks unit-ball vectors and zero total on the actual generated stream. This is the general algorithm class needed by the lower bounds; it is not restricted to Algorithm 1. Unreachable histories may be assigned arbitrary outputs. Dummy local tree histories let the existing output and residual functions apply without changing the placement process.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; §1, pp.1–2; §5.1, p.20

import Definitions.Def_OnlineSteinitz_Reduction_Randomness

open MeasureTheory
open scoped BigOperators

namespace OnlineSteinitz.Reduction.Supplement

/-! Immediate causal slot decisions: §1 pp.1–2 and §5 p.20.
The whole private random seed is available from the start. No future vector is available.
Validity is required on every promised stream, for every seed (not merely almost surely).
An arbitrary source algorithm has a total extension off reachable promised histories. -/
abbrev OrderingRule (d : ℕ) (Ω : Type*) :=
  Ω → List (ℕ × Vec d) → Vec d → ℕ

def orderingStep {T d : ℕ} {Ω : Type*} (A : OrderingRule d Ω)
    (ω : Ω) (r : Run T (Vec d)) (x : Vec d) : Run T (Vec d) :=
  ⟨fun _ => [], r.placed ++ [(A ω r.placed x, x)]⟩

def orderingRun {T d : ℕ} {Ω : Type*} (A : OrderingRule d Ω)
    (ω : Ω) (v : Fin T → Vec d) : Run T (Vec d) :=
  (List.ofFn v).foldl (orderingStep A ω) (emptyRun T (Vec d))

def LegalInput {T d : ℕ} (v : Fin T → Vec d) : Prop :=
  (∀ i, ‖v i‖ ≤ 1) ∧ ∑ i, v i = 0

def ValidOrdering {T d : ℕ} {Ω : Type*} (A : OrderingRule d Ω) : Prop :=
  ∀ ω (v : Fin T → Vec d), LegalInput v →
    ((orderingRun A ω v).placed.map Prod.fst).Nodup ∧
    ∀ p ∈ (orderingRun A ω v).placed, p.1 < T

def MeasurableOrdering {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : OrderingRule d Ω) : Prop :=
  ∀ h x, Measurable (fun ω => A ω h x)

/-! The adversary reads precisely the prior vector/placement history (§1 p.2).
These definitions are independent of the tree-router subclass. -/
def adaptiveOrderingRun {T d : ℕ} (A : OrderingRule d Unit)
    (adv : ℕ → List (ℕ × Vec d) → Vec d) : Run T (Vec d) :=
  (List.range T).foldl
    (fun r t => orderingStep A () r (adv t r.placed)) (emptyRun T (Vec d))

def LegalAdaptiveRun {T d : ℕ} (r : Run T (Vec d)) : Prop :=
  (∀ p ∈ r.placed, ‖p.2‖ ≤ 1) ∧ (r.placed.map Prod.snd).sum = 0

end OnlineSteinitz.Reduction.Supplement


