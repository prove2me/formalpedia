-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Inner
-- name    : NearLinearRSP_TwoResources_Inner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:19.089751+00:00
-- url     : https://prove2.me/theorems/f40bd366-a7ba-4831-97b9-0d78e026cf75
-- title:
--   Poisson parameters and the actual queue-built DP table
-- statement:
--   An inner call consists of an RSP instance, an accuracy $0<\delta<1$, a length threshold $L>0$ and a budget $C>0$. Set
--   $$
--   q=\lceil512/\delta^2\rceil,\qquad
--   \lambda_\ell=\frac{q}{(1+\delta/2)L},\qquad
--   \lambda_c=\frac{q}{(1+\delta/2)C}.
--   $$
--   The probability of $r$ ticks at mean $\mu$ is $e^{-\mu}\mu^r/r!$, including the point mass at zero when $\mu=0$. Length and cost increments are independent. The DP table and its parents and extraction ranks are computed by the nested decreasing-index queue construction of Section 4. Saturation $i\ge q$ or $j\ge q$ has value one, including at the source; the source has value zero only below both boundaries.
--
--   At each layer the source key is zero and every other active key is the minimum of its two next-tick values. Extract a minimum key, finalize it, and relax outgoing edges to vertices still in the queue only when the finite Poisson rectangle plus overflow gives a strictly smaller key. Equality ties preserve the first active vertex; equal initial tick choices choose length. Input self-loops are ignored during construction. Targets are accepted exactly at $\mathrm{DP}(t,0,0)\le1/4$.
--
--   This is a definition of the computation, rather than a table assumed to satisfy Bellman inequalities. The expectation uses $0\le a<q-i$ and $0\le b<q-j$, with overflow probability one minus that rectangle's total mass.
--
--   **Formalization Note** Active vertices suffice; every other table cell retains the value-one default. There is no real-RAM primitive for these definitions: implementing this computation and charging its operations are conclusions of the goal theorem.
--
--   The Poisson coefficients use the published definition `ActuarialValuation.poissonCountMass`, whose formula is identical, including the zero-rate case; it introduces no added hypothesis.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), pp.6–7, Section 4, Parameters and displayed update (✣); p.3 zero-weight convention

import Definitions.Def_NearLinearRSP_TwoResources_Instance
import Definitions.Def_actuarial_poissonCountMass

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

/-- Parameters of an inner call. Positivity is needed only for these normalized calls. -/
structure InnerInput where
  I : Instance
  δ : ℝ
  accuracy_pos : 0 < δ
  accuracy_lt_one : δ < 1
  L : ℝ
  length_pos : 0 < L
  budget_pos : 0 < (I.budget : ℝ)

noncomputable def tickLimit (A : InnerInput) : ℕ := Nat.ceil (512 / A.δ ^ 2)
noncomputable def lengthRate (A : InnerInput) : ℝ := tickLimit A / ((1 + A.δ / 2) * A.L)
noncomputable def costRate (A : InnerInput) : ℝ :=
  tickLimit A / ((1 + A.δ / 2) * A.I.budget)
noncomputable def zValue (A : InnerInput) : ℝ := (1 + A.δ / 2) / (1 + A.δ)

noncomputable def edgeMass (A : InnerInput) (u v a b : ℕ) : ℝ :=
  ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a *
    ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b

inductive Parent where
  | none
  | lengthTick
  | costTick
  | edge (u : ℕ)
  deriving DecidableEq

structure Cell where
  value : ℝ
  parent : Parent
  rank : ℕ

abbrev Table := ℕ → ℕ → ℕ → Cell

def putCell (T : Table) (v i j : ℕ) (c : Cell) : Table :=
  fun w a b => if w = v ∧ a = i ∧ b = j then c else T w a b

/-- Saturation has precedence over the source boundary, including beyond q. -/
noncomputable def dpValue (A : InnerInput) (T : Table) (v i j : ℕ) : ℝ :=
  if tickLimit A ≤ i ∨ tickLimit A ≤ j then 1 else (T v i j).value

/-- Finite-rectangle Poisson expectation with its exact overflow mass. -/
noncomputable def edgeExpectation (A : InnerInput) (T : Table) (u v i j : ℕ) : ℝ :=
  if tickLimit A ≤ i ∨ tickLimit A ≤ j then 1 else
    1 - (∑ a ∈ Finset.range (tickLimit A - i),
      ∑ b ∈ Finset.range (tickLimit A - j), edgeMass A u v a b) +
    ∑ a ∈ Finset.range (tickLimit A - i),
      ∑ b ∈ Finset.range (tickLimit A - j),
        edgeMass A u v a b * dpValue A T u (i + a) (j + b)

/-- Stable first-minimum selection; it makes all ties independent of correctness. -/
noncomputable def firstMin {α : Type} (score : α → ℝ) (xs : List α) (fallback : α) : α :=
  xs.foldl (fun x y => if score y < score x then y else x) (xs.headD fallback)

structure LayerState where
  table : Table
  keys : ℕ → ℝ
  parents : ℕ → Parent
  queue : List ℕ
  nextRank : ℕ

noncomputable def initLayer (A : InnerInput) (T : Table) (i j : ℕ) : LayerState where
  table := T
  keys v := if v = A.I.source then 0 else
    min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))
  parents v := if v = A.I.source then .none else
    if dpValue A T v (i + 1) j ≤ dpValue A T v i (j + 1) then .lengthTick else .costTick
  queue := activeVertices A.I
  nextRank := 0

noncomputable def relaxEdge (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) : LayerState :=
  if e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue then
    let k := edgeExpectation A S.table e.1 e.2 i j
    if k < S.keys e.2 then
      { S with
        keys := Function.update S.keys e.2 k
        parents := Function.update S.parents e.2 (.edge u) }
    else S
  else S

noncomputable def popLayer (A : InnerInput) (i j : ℕ) (S : LayerState) : LayerState :=
  match S.queue with
  | [] => S
  | v :: _ =>
    let u := firstMin S.keys S.queue v
    let c : Cell := ⟨S.keys u, S.parents u, S.nextRank⟩
    let S' : LayerState := { S with
      table := putCell S.table u i j c
      queue := S.queue.erase u
      nextRank := S.nextRank + 1 }
    A.I.graph.edges.foldl (relaxEdge A i j u) S'

noncomputable def buildLayer (A : InnerInput) (T : Table) (i j : ℕ) : Table :=
  ((List.range (activeVertices A.I).length).foldl
    (fun S _ => popLayer A i j S) (initLayer A T i j)).table

/-- The actual queue construction, in decreasing i and then decreasing j. -/
noncomputable def buildTable (A : InnerInput) : Table :=
  ((List.range (tickLimit A)).reverse).foldl (fun T i =>
    ((List.range (tickLimit A)).reverse).foldl (fun U j => buildLayer A U i j) T)
    (fun _ _ _ => ⟨1, .lengthTick, 0⟩)

noncomputable def accepted (A : InnerInput) (t : ℕ) : Prop :=
  dpValue A (buildTable A) t 0 0 ≤ 1 / 4

end NearLinearRSP.TwoResources


