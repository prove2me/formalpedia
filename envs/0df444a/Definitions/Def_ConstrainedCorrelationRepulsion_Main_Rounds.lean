-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Rounds
-- name    : ConstrainedCorrelationRepulsion_Main_Rounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:29:54.797683+00:00
-- url     : https://prove2.me/theorems/cb4c366a-3c8b-4130-84ed-3ef8f7230136
-- title:
--   Fixed independent rounds and first-hit accounting
-- statement:
--   Independent coordinates of a countable product measure supply candidates from the original fixed Figure 5 law. The current intersection is repaired before it is removed. The infinite partition uses first processing times and repaired blocks; never-hit vertices receive separate labels on the nontermination event. Almost-sure termination is a conclusion, not an input assumption. Finite completion places each remaining unit in its own cluster.
--
--   The pair charge is $F_a(x,y)=[2a(1-y)+(1-a+a b(x))y]/(2-y)$. Both actual and target pair probabilities enter the error expressions. Nonnegative extended integrals define expected costs. The round count is $n\lceil\log_2(n^2/\tau)\rceil$. The internal level is $r=2\lceil256(60007)^2/\varepsilon_c^2\rceil$, with rational $0<\varepsilon_c\le1$ and $\tau=\varepsilon_c/4$.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), §§6.2–6.3, equations (37)–(43), printed pp.31–35 (PDF pp.32–36)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Sampler
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

/-- Function (38), defined from labels, LP distances and the actual pair probability. -/
noncomputable def firstHitCharge (a x y : ℝ) : ℝ :=
  (2 * a * (1-y) + (1-a+a*b x)*y) / (2-y)

/-- One fixed-law candidate stream; intersections precede repair. -/
noncomputable def processedBefore {n : ℕ} (stream : ℕ → Finset (Fin n)) (t : ℕ) : Finset (Fin n) :=
  (Finset.range t).biUnion stream

noncomputable def roundBlocks {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (stream : ℕ → Finset (Fin n)) (t : ℕ) : List (Finset (Fin n)) :=
  repair I x (stream t \ processedBefore stream t)

noncomputable def finitePartition {n : ℕ} (I : Instance n) (U : Units n)
    (x : Fin n → Fin n → ℝ) (stream : ℕ → Finset (Fin n)) (T : ℕ) : Partition n :=
  partitionOfBlocks (((List.range T).flatMap (roundBlocks I x stream)) ++
    (U.blocks.filter (fun B => Disjoint B (processedBefore stream T))).toList)

noncomputable def firstTime {n : ℕ} (stream : ℕ → Finset (Fin n)) (v : Fin n) : Option ℕ :=
  if h : ∃ t, v ∈ stream t then some (Nat.find h) else none

/-- The infinite output is a partition even on the null event of nontermination: an unhit
vertex is given its own label. This default is disjoint from all processed labels. -/
noncomputable def infiniteLabel {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (stream : ℕ → Finset (Fin n)) (v : Fin n) : Sum (Fin n) (ℕ × Fin n) :=
  match firstTime stream v with
  | none => Sum.inl v
  | some t => Sum.inr (t, partitionOfBlocks (roundBlocks I x stream t) v)

/-- Canonical vertex representatives of the equivalence classes of the infinite labels. -/
noncomputable def infinitePartition {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (stream : ℕ → Finset (Fin n)) : Partition n := fun v =>
  let C := Finset.univ.filter (fun u => infiniteLabel I x stream u = infiniteLabel I x stream v)
  C.min' (by exact ⟨v, by simp [C]⟩)

/-- A genuine countable product probability space: no independent-stream assumption is
supplied by a theorem's caller. Each coordinate has the original fixed candidate law. -/
noncomputable def streamMeasure {n : ℕ} (law : PMF (Finset (Fin n))) :
    Measure (ℕ → Finset (Fin n)) :=
  Measure.infinitePi (fun _ : ℕ => law.toMeasure)

noncomputable def infiniteExpectedCost {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ stream, ENNReal.ofReal (cost I (infinitePartition I (tableDistance U y) stream) : ℝ)
    ∂streamMeasure (candidateLaw I U y r)

noncomputable def finiteExpectedCost {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r T : ℕ) : ℝ≥0∞ :=
  ∫⁻ stream, ENNReal.ofReal (cost I (finitePartition I U (tableDistance U y) stream T) : ℝ)
    ∂streamMeasure (candidateLaw I U y r)

noncomputable def roundsBound {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) : ℝ :=
  2 * L I U y - Lminus I U y + 2 * Y U y / r +
    3 * Real.sqrt (2 * Y U y * positivePairs I U / r)

noncomputable def roundCount (n : ℕ) (tau : ℚ) : ℕ :=
  n * ⌈Real.logb 2 ((n : ℝ)^2 / (tau : ℝ))⌉₊

noncomputable def level (epsilon : ℚ) : ℕ :=
  2 * ⌈256 * ((Cpre + 1 : ℕ) : ℝ)^2 / (epsilon : ℝ)^2⌉₊

end ConstrainedCorrelationRepulsion.Main


