-- Prove2me | Definitions.Def_SkewMatching_ProcState
-- name    : SkewMatching_ProcState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:34.779683+00:00
-- url     : https://prove2.me/theorems/31698cb8-9a60-4459-8304-d8bc9a45a449
-- title:
--   §3.3 — the algorithm as a Markov chain, for every search policy
-- statement:
--   This definition writes the algorithm of §3.3 as a process, given a skew-symmetric graph $G$, a source $s$, parameters $K$ and $U$, and a **reachability policy**: a deterministic map from the current flow, variables, sub-multigraph $H$ and partition to either a regular $s$–$s'$ path in $H$ or the next partition, which must be a pause of $H$ obtained from the previous one by Grow and Merge.
--
--   A state holds the flow $f$, the variables $x_e$, $H$, the partition, the number of barrier toggle operations made, and a status. From the initial state ($f=0$, $x\equiv 1$, $H=\emptyset$, the initial partition) a step of a searching state does the following.
--
--   1. Sample an active edge $e$ with probability proportional to $|d_e|/x_e$. If all these weights vanish, move to the absorbing status `noEdge`.
--   2. If $d_e<0$: replace $x_e$ by $\max\{1,x_e/2\}$, add $\{e,e'\}$ to $H$ and call the policy.
--   3. If $d_e>0$: multiply $x_e$ by $3/2$, and declare failure if the result exceeds $U$.
--   4. If the policy returns a path: augment along it and its symmetric path, set $x=1$ on each edge that becomes active, reset $H$ and the partition, and stop once the flow value has grown by at least $K/2$.
--
--   The pair $(e,e')$ shares one variable. Terminal statuses repeat forever. The law after $t$ steps is the $t$-fold iterate of this kernel.
--
--   **Formalization Note** The paper's search is only sketched, and it fixes no scanning order, so the process is parametrised by the policy. Other variables are not reset on augmentation: the paper initializes them once. The status `noEdge` keeps the kernel total; Lemma 15 excludes it under the hypotheses of Lemma 14.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.3, pp.7–8; Definition 13, p.7; §2.3, p.5; Lemma 23, pp.15–16

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph_IsFlow
import Definitions.Def_SkewMatching_SkewGraph_doubled
import Definitions.Def_SkewMatching_SkewGraph_charge
import Definitions.Def_SkewMatching_SkewGraph_GMStep

namespace SkewMatching

open scoped Classical

/-- A deterministic **regular reachability policy** for the residual graphs of `G` from the source `s`: from the current flow `f`, the
variables `x`, the current sub-multigraph `H` of the residual graph, and the current partition, it returns a regular `s`–`s′` path in `H` or
the next partition. It obeys **Lemma 23**, p.16: (Pause) a returned partition is a barrier of `H` with `A ∪ ⋃X_i` the set reachable by regular
paths; (Progress) it arises from the previous partition by a finite sequence of Grow and Merge.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 23, pp.15–16;
Algorithm, step 2, p.7.

**Formalization Note.** The algorithm's search is only sketched in the paper, and it fixes no scanning order. A theorem about every policy
covers the paper's search, which is one of them. The obligations bind only on valid inputs: `H` is `σ`-closed and the partition is a pause of a
sub-multigraph of `H`. -/
structure ReachPolicy {V E : Type*} [Fintype V] (G : SkewGraph V E) (s : V) where
  search : (E → ℕ) → (E × Bool → ℝ) → Finset (E × Bool) → Partition V →
    List (E × Bool) ⊕ Partition V
  path_spec : ∀ f x H P p, G.doubled.SymmClosed H →
    (∃ H₀ ⊆ H, G.doubled.Paused s H₀ P) → search f x H P = .inl p →
      G.doubled.IsRegularPathIn H s (G.σV s) p
  pause_spec : ∀ f x H P P', G.doubled.SymmClosed H →
    (∃ H₀ ⊆ H, G.doubled.Paused s H₀ P) → search f x H P = .inr P' →
      G.doubled.GMSeq H P P' ∧ G.doubled.IsPause H s P'

/-- The status of the algorithm of §3.3. `noEdge` is the absorbing case in which no active edge has nonzero sampling weight. -/
inductive Status : Type
  | searching
  | failed
  | done
  | noEdge
  deriving DecidableEq

/-- A state of the algorithm of §3.3, pp.7–8: the flow, the variables `x_e`, the sub-multigraph `H`, the partition, the number of barrier
toggle operations made so far, and the status. Only the values of `x` on active edges are read. -/
structure ProcState (V E : Type*) where
  f : E → ℕ
  x : E × Bool → ℝ
  H : Finset (E × Bool)
  part : Partition V
  toggles : ℕ
  status : Status

namespace ProcState

variable {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (s : V) (K : ℕ) (U : ℝ)
  (π : ReachPolicy G s)

/-- The initial state: `x_e = 1`, zero flow, `H` empty, the initial partition (which is the first pause on the empty `H`). -/
def init : ProcState V E where
  f := fun _ => 0
  x := fun _ => 1
  H := ∅
  part := SkewGraph.startPart s
  toggles := 0
  status := .searching

/-- The sampling weight `|d_e| w_e = |d_e| / x_e` of an active edge (Definition 13, p.7), and `0` on an inactive edge. -/
noncomputable def weight (σ : ProcState V E) (a : E × Bool) : ENNReal :=
  if SkewGraph.Active σ.f a then
    ENNReal.ofReal (|((G.doubled.charge K σ.H σ.part a : ℤ) : ℝ)| / σ.x a)
  else 0

/-- Set the variable of the pair `(a, a′)`: "x_e and x_e′ refer to the same variable" (p.5). -/
noncomputable def setPair (x : E × Bool → ℝ) (a : E × Bool) (v : ℝ) : E × Bool → ℝ :=
  fun b => if b = a ∨ b = G.doubled.σE a then v else x b

/-- Step 6, p.8: augment along the path and its symmetric path, give every edge that becomes active the variable `1`, and restart with `H` empty.
The algorithm is `done` once the flow value has grown by at least `K/2`. Other variables are not reset. -/
noncomputable def afterAugment (σ : ProcState V E) (p : List (E × Bool)) : ProcState V E :=
  let f' := G.augment σ.f p
  { f := f'
    x := fun a => if SkewGraph.Active f' a ∧ ¬ SkewGraph.Active σ.f a then 1 else σ.x a
    H := ∅
    part := SkewGraph.startPart s
    toggles := σ.toggles
    status := if (K : ℤ) ≤ 2 * G.value s f' then .done else .searching }

/-- Steps 3–6, pp.7–8, once the edge `a` has been sampled. A negative charge halves `x_a`, clips it at `1`, adds `{a, a′}` to `H` and resumes the
search. A positive charge multiplies `x_a` by `3/2`, and declares failure if that exceeds `U`. -/
noncomputable def afterSample (σ : ProcState V E) (a : E × Bool) : ProcState V E :=
  let d := G.doubled.charge K σ.H σ.part a
  if d < 0 then
    let x' := setPair G σ.x a (max 1 (σ.x a / 2))
    let H' := σ.H ∪ {a, G.doubled.σE a}
    match π.search σ.f x' H' σ.part with
    | .inl p => afterAugment G s K { σ with x := x', toggles := σ.toggles + 1 } p
    | .inr P' => { σ with x := x', H := H', part := P', toggles := σ.toggles + 1 }
  else if 0 < d then
    let v := σ.x a * (3 / 2)
    { σ with x := setPair G σ.x a v, toggles := σ.toggles + 1,
             status := if U < v then .failed else .searching }
  else σ

lemma tsum_weight_ne_top (σ : ProcState V E) : ∑' a, weight G K σ a ≠ ⊤ := by
  rw [tsum_fintype]
  refine ENNReal.sum_ne_top.mpr fun a _ => ?_
  unfold weight
  split_ifs <;> simp

/-- One step of the algorithm. Terminal statuses stutter. A `searching` state samples an active edge with probability proportional to `|d_e| w_e`
(Definition 13, p.7), and moves to `noEdge` if all those weights vanish. -/
noncomputable def step (σ : ProcState V E) : PMF (ProcState V E) :=
  if σ.status ≠ .searching then PMF.pure σ
  else if h : ∑' a, weight G K σ a = 0 then PMF.pure { σ with status := .noEdge }
  else (PMF.normalize (weight G K σ) h (tsum_weight_ne_top G K σ)).map (afterSample G s K U π σ)

/-- The law of the state after `t` steps from `init`. -/
noncomputable def law : ℕ → PMF (ProcState V E)
  | 0 => PMF.pure (init s)
  | t + 1 => (law t).bind (step G s K U π)

end ProcState

end SkewMatching


