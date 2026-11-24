-- Prove2me | Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_Algorithm3
-- name    : RiskAverseSDDP_Subdiff_Supplement_Algorithm3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:32:04.014791+00:00
-- url     : https://prove2.me/theorems/c53f9650-8b19-4016-9567-acdaf2b6c757
-- title:
--   Algorithm 3 — decisions at every node and on-path and off-path cuts
-- statement:
--   A run of Algorithm 3 records decisions, cut intercepts and slopes, and approximate recourse functions at every node. At iteration $k+1$, each node's decision minimizes its realization-dependent cost plus its own continuation approximation from iteration $k$, over its feasible set. All nodes are evaluated, including nodes off the sampled path.
--
--   At a nonleaf sampled node, compute the child subproblem values, choose a density attaining the node risk supremum, choose child value-function subgradients and form the risk-weighted intercept and slope (6.49). At a nonleaf node off the sampled path, take the old approximation's value and a subgradient at the current history, as in (6.47). Update the approximation by taking the maximum of the previous approximation and the new affine cut. Leaves have zero approximations and cut coefficients. Initially all nonleaf approximations are identically $-\infty$.
--
--   **Formalization Note** Fixed deterministic choice rules are used, as in Algorithm 2. Slopes in (6.48) may be any subgradients of the indicated value function; this enlarges the permitted choices and includes the printed multiplier formulas. An initial constant $-\infty$ objective is minimized by any feasible decision, consistent with (6.45); a finite epigraph minimizer for (6.46) is not asserted. Once values are finite the ordinary epigraph interpretation applies. The full ancestor history has its Euclidean norm. This definition is the full arbitrary finite-tree algorithm, separate from the concrete counterexample instance.
-- source:
--   Guigues, arXiv:1408.4439v4, pp. 19–20, Algorithm 3, (6.45), (6.47)–(6.49)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_TreeModel

namespace RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence

/-- Choice rules for Algorithm 3: minimizers at each node, risk-maximizing densities,
child value-function subgradients, and subgradients of the old approximation off the sampled
path. These are the same deterministic-choice convention used for Algorithm 2. -/
structure TreeRules {T n q p : ℕ} {V : ℕ → Type*} (D : TreeModel T n q p V) where
  xRule : (s : ℕ) → V s → Hist n s → (Hist n (s + 1) → EReal) → EuclideanSpace ℝ (Fin n)
  pRule : (s : ℕ) → (ν : V s) → (D.Child s ν → EReal) → (D.Child s ν → ℝ)
  πRule : (s : ℕ) → (ν : V s) → (m : D.Child s ν) → Hist n (s + 1) →
    (Hist n (s + 2) → EReal) → Hist n (s + 1)
  offRule : (s : ℕ) → V s → Hist n (s + 1) → (Hist n (s + 1) → EReal) → Hist n (s + 1)

/-- Algorithm 3 computes decisions at every node, including off the sampled path.
The approximation at a node of stage `s+1` is a function on its full history of length s+1. -/
structure TreeRunData (n : ℕ) (V : ℕ → Type*) where
  x : ℕ → (s : ℕ) → V s → EuclideanSpace ℝ (Fin n)
  θ : ℕ → (s : ℕ) → V s → EReal
  β : ℕ → (s : ℕ) → V s → Hist n (s + 1)
  Qm : ℕ → (s : ℕ) → V s → Hist n (s + 1) → EReal

namespace TreeRunData

variable {T n q p : ℕ} {V : ℕ → Type*} (r : TreeRunData n V)

/-- Decisions on the actual ancestor chain of the given node, in Euclidean history space. -/
def hist (D : TreeModel T n q p V) (k : ℕ) : (s : ℕ) → V s → Hist n (s + 1)
  | 0, ν => (Hist.empty n).snoc (r.x k 0 ν)
  | s + 1, ν => (hist D k s (D.parent s ν)).snoc (r.x k (s + 1) ν)

def phist (D : TreeModel T n q p V) (k : ℕ) : (s : ℕ) → V s → Hist n s
  | 0, _ => Hist.empty n
  | s + 1, ν => r.hist D k s (D.parent s ν)

end TreeRunData

namespace TreeModel

variable {T n q p : ℕ} {V : ℕ → Type*} [∀ s, Fintype (V s)]

/-- Algorithm 3, pp. 19-20, including both off-path (6.47) and on-path (6.49) cuts.
Subgradients in the multiplier formula (6.48) are represented by their subgradient
inequality, a disclosed generalization. Initial constant -infinity objectives use feasible
extended-real minimizers; no finite epigraph minimizer is asserted at startup. -/
def IsRun3 (D : TreeModel T n q p V) (R : TreeRules D) (ys : ℕ → D.Path)
    (r : TreeRunData n V) : Prop :=
  letI : ∀ s, DecidableEq (V s) := fun _ => Classical.decEq _
  (∀ s, s + 1 < T → ∀ ν : V s, r.Qm 0 s ν = fun _ => ⊥) ∧
  (∀ k s, s + 1 = T → ∀ ν : V s,
    r.Qm k s ν = (fun _ => 0) ∧ r.θ k s ν = 0 ∧ r.β k s ν = 0) ∧
  (∀ k s, s < T → ∀ ν : V s,
    let x := r.phist D (k + 1) s ν
    let y := r.x (k + 1) s ν
    y = R.xRule s ν x (r.Qm k s ν) ∧ y ∈ D.feas s ν x ∧
    ∀ z ∈ D.feas s ν x,
      D.f s ν (x.snoc y) + r.Qm k s ν (x.snoc y) ≤
        D.f s ν (x.snoc z) + r.Qm k s ν (x.snoc z)) ∧
  (∀ k s (hs : s + 1 < T) (ν : V s),
    let xt := r.hist D (k + 1) s ν
    (if ν = ys (k + 1) ⟨s, by omega⟩ then
      let Z : D.Child s ν → EReal := fun m => D.stageVal (s + 1) m.val (r.Qm k (s + 1) m.val) xt
      let pk := R.pRule s ν Z
      pk ∈ D.Prisk s ν ∧ D.wsum s ν pk Z = D.rho s ν Z ∧
      (∀ m : D.Child s ν,
        R.πRule s ν m xt (r.Qm k (s + 1) m.val) ∈
          ESubdiff (fun z => D.stageVal (s + 1) m.val (r.Qm k (s + 1) m.val) z) xt) ∧
      r.θ (k + 1) s ν = D.wsum s ν pk Z ∧
      r.β (k + 1) s ν =
        ∑ m : D.Child s ν, (pk m * D.Φ s ν m) • R.πRule s ν m xt (r.Qm k (s + 1) m.val)
    else
      r.θ (k + 1) s ν = r.Qm k s ν xt ∧
      r.β (k + 1) s ν = R.offRule s ν xt (r.Qm k s ν) ∧
      r.β (k + 1) s ν ∈ ESubdiff (r.Qm k s ν) xt) ∧
    r.Qm (k + 1) s ν = fun z =>
      max (r.Qm k s ν z)
        (r.θ (k + 1) s ν + ((inner ℝ (r.β (k + 1) s ν) (z - xt) : ℝ) : EReal)))

end TreeModel

end RiskAverseSDDP.Subdiff.Supplement


