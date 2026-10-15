-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
-- name    : OAI_Analysis_LipschitzFree_StatePaths
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:10:27.694543+00:00
-- url     : https://prove2.me/theorems/5fce935a-ca54-4a3a-91ca-1bbb3f885061
-- title:
--   Paths of a transition relation on a set of states
-- statement:
--   Let $S$ be a set of states and $r$ a binary relation on $S$ (the transitions; write $r(j,k)$). For $j\in S$ and $n\in\mathbb{N}$, an $r$-path of length $n$ based at $j$ is a sequence of states
--   $$j=s_0,\ s_1,\ \dots,\ s_n\qquad\text{with } r(s_{t-1},s_t)\ \text{ for } 1\le t\le n .$$
--
--   1. **Based paths.** $\mathrm{Based}_r(j,n)$ is the set of $r$-paths of length $n$ based at $j$, built recursively: $\mathrm{Based}_r(j,0)$ has exactly one element (the path consisting of $j$ alone), and an element of $\mathrm{Based}_r(j,n+1)$ is a pair consisting of a successor $k$ with $r(j,k)$ and a path in $\mathrm{Based}_r(k,n)$. It is finite when $S$ is finite.
--   2. **Vertices of a path.** For $\pi\in\mathrm{Based}_r(j,n)$ and $t\in\{0,\dots,n\}$, $\pi(t)\in S$ is its $t$-th state. One has $\pi(0)=j$, and for a path of length $n+1$ with chosen successor $k$ and tail path $\pi'\in\mathrm{Based}_r(k,n)$, $\pi(t+1)=\pi'(t)$ for $0\le t\le n$.
--   3. **All paths.** $\mathrm{Path}_r(n)=\bigsqcup_{j\in S}\mathrm{Based}_r(j,n)$ is the set of all $r$-paths of length $n$ with arbitrary starting state, finite when $S$ is finite, with the same vertex map $\pi\mapsto(\pi(0),\dots,\pi(n))$.
--
--   These paths are used to count the state sequences that accompany walks in a port graph: in the construction the states are points of a finite subset of the metric block and transitions join nearby points, so a bound on the number of $r$-successors of each state bounds the number of paths.
--
--   **Formalization Note** `StatePaths.Based r j n` is a dependent type defined by recursion on $n$ (`PUnit` for $n=0$, and a `Sigma` type over the subtype of successors for $n+1$), in the same universe as $S$; `vertex` is indexed by `Fin (n+1)` with the simp lemmas `at_zero` and `at_succ`; `Path r n` is the `Sigma` type over the starting state and `Path.vertex` its vertex map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/StatePaths.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/StatePaths.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words

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


