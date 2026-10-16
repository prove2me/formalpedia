-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:05:49.360341+00:00
-- url     : https://prove2.me/theorems/40e56285-4c06-433e-880c-bb8fcf5baa78
-- title:
--   Paths of a transition relation on a set of states and their state sequences
-- statement:
--   Let $S$ be a set of states and $r$ a binary relation on $S$ (the allowed transitions). This file defines finite paths of $r$ and their sequences of visited states.
--
--   1. **Based paths.** For $j\in S$ and $n\in\mathbb{N}$, a path of length $n$ based at $j$ is defined recursively: for $n=0$ there is exactly one (empty) path, and a path of length $n+1$ based at $j$ consists of a state $k$ with $r(j,k)$ together with a path of length $n$ based at $k$. Mathematically it is a sequence of states
--   $$j=s_0,\ s_1,\ \dots,\ s_n\qquad\text{with } r(s_{t-1},s_t)\ \text{ for } 1\le t\le n .$$
--   2. **Visited states.** A based path $p$ of length $n$ determines its vertex map $t\mapsto s_t$ for $t\in\{0,1,\dots,n\}$; it satisfies $s_0=j$, and the state at position $t+1$ of a path based at $j$ is the state at position $t$ of its tail, which is based at the first chosen successor $k$.
--   3. **Paths.** A path of length $n$ is a pair consisting of a starting state $j\in S$ and a path of length $n$ based at $j$; its vertex map is that of the based path.
--
--   When $S$ is finite, the sets of based paths and of paths of each length are finite. These objects are used to count sequences of states with bounded transitions, for instance the state sequences that accompany walks in a port graph.
--
--   **Formalization Note** `StatePaths.Based r j n` is defined by recursion on $n$ as `PUnit` for $n=0$ and as a dependent sum over successors $k$ with $r(j,k)$ for $n+1$; `StatePaths.vertex` (with `at_zero`, `at_succ`) is the vertex map, and `StatePaths.Path r n` is the dependent sum over starting states with `Path.vertex`. Finiteness is provided by `Fintype` instances when $S$ is a finite type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/StatePaths.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/StatePaths.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming

namespace OAI

/-!
# Counting finite-state paths with bounded transitions
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.StatePaths
open scoped BigOperators Classical

universe u
variable {S : Type u} (r : S → S → Prop)

def Based : S → ℕ → Type u
  | _, 0 => PUnit
  | j, n+1 => Σ k : {k : S // r j k}, Based k.val n

instance [Fintype S] (j : S) (n : ℕ) : Fintype (Based r j n) := by
  induction n generalizing j with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI (k : S) : Fintype (Based r k n) := ih k
    exact inferInstanceAs (Fintype (Σ k : {k : S // r j k}, Based r k.val n))

def vertex (j : S) : {n : ℕ} → Based r j n → Fin (n+1) → S
  | 0, _, _ => j
  | _n+1, p, i => Fin.cases j (fun i => vertex p.1.val p.2 i) i

@[simp] theorem at_zero (j : S) (n : ℕ) (p : Based r j n) : vertex r j p 0 = j := by
  cases n <;> rfl

@[simp] theorem at_succ (j : S) (n : ℕ) (p : Based r j (n+1)) (i : Fin (n+1)) :
    vertex r j p i.succ = vertex r p.1.val p.2 i := rfl

def Path (n : ℕ) := Σ j : S, Based r j n

instance [Fintype S] (n : ℕ) : Fintype (Path r n) := inferInstanceAs (Fintype (Σ j : S, Based r j n))

def Path.vertex {n : ℕ} (p : Path r n) : Fin (n+1) → S := StatePaths.vertex r p.1 p.2

end DiscreteFree.StatePaths

end

end

end OAI


