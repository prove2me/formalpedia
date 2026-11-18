-- Prove2me | Definitions.Def_KoanaKPaths_GraphDP
-- name    : KoanaKPaths_GraphDP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T01:44:13.200573+00:00
-- url     : https://prove2.me/theorems/27595c39-37f4-43a1-a1e9-04db4df3c261
-- title:
--   Exterior-algebra dynamic program for directed walks
-- statement:
--   For a directed graph with arc set $A$, label each vertex $v$ by its sign vector $\sigma_v\in\mathbb Z^k$. Layer $p$, endpoint $v$ and sketch state $a$ store an exterior-coordinate array $F_{p,v,a}$. At the first layer,
--
--   $$F_{1,v,a}=R_1[a,v]\sigma_v.$$
--
--   For $2\le p\le k$, define
--
--   $$F_{p,v,a}=\left(\sum_{u:(u,v)\in A}\sum_b R_p[a,(b,v)]F_{p-1,u,b}\right)\wedge\sigma_v.$$
--
--   The output for state $a$ is the sum over terminal vertices of layer $k$. This specializes the paper's right-skew circuit evaluation to the directed-walk recurrence. Auxiliary prefix concatenation and sign-chain weights specify its relation to the recursive tensor sketch. Every array is indexed by the $2^k$ basis subsets; no list of walks is part of the state.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 8 / PDF p. 9, Section 3.2, equation (3.2) and the output-coefficient identity; printed p. 9 / PDF p. 10, Section 4.1, directed-walk recurrence. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphEstimator

noncomputable section
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

/-- Concatenate a prefix tuple with its residual word. -/
def joinWord {n k p : ℕ} (τ : Fin p → Fin n) (ρ : Resid n k p) : Fin k → Fin n :=
  fun r => if h : r.val < p then τ ⟨r.val,h⟩ else ρ ⟨r,by omega⟩

/-- Sum of the sketch sign products over the internal sketch states of a prefix word. -/
def chainWeight {n k ℓ : ℕ} (R : SketchSigns n k ℓ) :
    (p : ℕ) → (Fin p → Fin n) → Fin ℓ → ℤ
  | 0 => fun _ _ => 0
  | 1 => fun τ a => sgn (R.1 a (τ 0))
  | i+2 => fun τ a => if h : i < k-1 then
      ∑ b, sgn (R.2 ⟨i,h⟩ a (b,τ (Fin.last (i+1)))) *
        chainWeight R (i+1) (Fin.init τ) b
    else 0

/-- Exterior-algebra dynamic program for directed walks, with a state in the sketch width.
Layer `p`, vertex `v`, state `a` stores the signed sum of all `p`-vertex walks ending at `v`. -/
def graphLayer {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) : ℕ → Fin n → Fin ℓ → Coordinates k
  | 0 => fun _ _ => 0
  | 1 => fun v a => sgn (R.1 a v) • wordCoordinates [fun r => sgn (σ v r)]
  | i+2 => fun v a => if h : i < k-1 then
      wedgeRight (∑ u : Fin n, if (u,v) ∈ arcs.toFinset then
        ∑ b : Fin ℓ, sgn (R.2 ⟨i,h⟩ a (b,v)) • graphLayer arcs σ R (i+1) u b
        else 0) (fun r => sgn (σ v r))
    else 0

/-- Sum the terminal-vertex layers to obtain the output of the walk circuit. -/
def graphOutput {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (a : Fin ℓ) : Coordinates k :=
  ∑ v : Fin n, graphLayer arcs σ R k v a

end KoanaKPaths.Main


