-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_GraphLaws
-- name    : CoarseMatching_LowerBound_GraphLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:36:10.831262+00:00
-- url     : https://prove2.me/theorems/fa6a1d7e-e7f9-4b8e-8311-1659519073d1
-- title:
--   Shared-core random graphs and asymptotic parameter families
-- statement:
--   Let $U$ and $V$ each have $N$ labeled vertices. Sample one uniform core $C\subseteq U$ of size $h$. Conditional on that same core, independently draw each right vertex’s count and neighbor set using $P_b$. Its degree is $d$, and the graph has $2N$ vertices. The prescribed streams reveal right neighbor lists in label order; vertex arrival first announces all left vertices with empty lists. The hidden core is never passed to the estimator.
--
--   $$a=24c^2,\quad c\ge1,\quad1\le d\le h,\quad ah\le N,\quad a(N)/N\longrightarrow0.$$
--
--   A parameter family carries the count laws, sizes and real approximation factor for each $N$. Admissibility means eventual validity of the standing assumptions and the displayed limit. The graph probabilities and the estimator’s strict-threshold acceptance gap are computed from these laws, with threshold $N/(8c)$.
--
--   This family formulation retains both high-probability graph conclusions and their eventual test consequence without imposing false small-size bounds.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §4.1–§4.2, printed pp.11–13 (PDF pp.12–14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_HiddenCore
import Definitions.Def_CoarseMatching_LowerBound_Streaming

open MeasureTheory Filter

namespace CoarseMatching.LowerBound
noncomputable section

abbrev NeighborLists (N : ℕ) := Fin N → Finset (Fin N)

def left {N : ℕ} (i : Fin N) : Fin (N+N) := Fin.castAdd N i
def right {N : ℕ} (i : Fin N) : Fin (N+N) := Fin.natAdd N i

def hardColor (N : ℕ) (v : Fin (N+N)) : Bool := decide (N ≤ v.val)

/-- The canonical ordered stream in §4.1, printed p.11 / PDF p.12.
Every left vertex arrives first in vertex mode, followed by all right vertices.
The edge mode orders each neighbor list by increasing left label. -/
def hardStream {N : ℕ} (mode : Arrival) (B : NeighborLists N) : List (Update (N+N)) :=
  match mode with
  | .edge => (List.finRange N).flatMap (fun i =>
      (B i).sort (· ≤ ·) |>.map (fun u => Sum.inl (left u, right i)))
  | .vertex => ((List.finRange N).map (fun u => Sum.inr (left u, ∅))) ++
      ((List.finRange N).map (fun i => Sum.inr (right i, (B i).image left)))

def hardGraph {N : ℕ} (B : NeighborLists N) := streamGraph (hardStream .edge B)

/-- One shared uniformly sampled core, then conditionally independent neighbor lists.
Lists are sampled once and used for all passes. The core is absent from the stream. -/
def graphLaw (N h d : ℕ) (P : CountLaw d) : PMF (NeighborLists N) :=
  (subsetLaw (Finset.univ : Finset (Fin N)) h).bind fun C =>
    (iid (P.bind (fun z => neighborLaw C d z.val)) N).map
      (fun bs i => bs[i.val]?.getD ∅)

structure GraphParameters (N : ℕ) where
  c : ℝ
  a : ℝ
  d : ℕ
  h : ℕ
  P₀ : CountLaw d
  P₁ : CountLaw d

/-- All standing assumptions of §4.1. a is real, as a=24c² in the source. -/
def GraphParameters.Valid {N : ℕ} (F : GraphParameters N) : Prop :=
  1 ≤ F.c ∧ F.a = 24*F.c^2 ∧ 1 ≤ F.d ∧ F.d ≤ F.h ∧
    F.a*(F.h : ℝ) ≤ (N : ℝ) ∧ EquationFour F.a F.P₀ F.P₁

/-- Family meaning of a=o(N); no assertion of an asymptotic condition on a scalar. -/
def Admissible (F : (N : ℕ) → GraphParameters N) : Prop :=
  (∀ᶠ N in atTop, (F N).Valid) ∧
    Tendsto (fun N => (F N).a/(N : ℝ)) atTop (nhds 0)

def coverProbability (N : ℕ) (F : GraphParameters N) : ℝ :=
  ((graphLaw N F.h F.d F.P₀).toOuterMeasure
    {B | (vc (hardGraph B) : ℝ) ≤ 3*(N : ℝ)/F.a}).toReal

def matchingProbability (N : ℕ) (F : GraphParameters N) : ℝ :=
  ((graphLaw N F.h F.d F.P₁).toOuterMeasure
    {B | (N : ℝ)/4 ≤ (mm (hardGraph B) : ℝ)}).toReal

def graphAcceptance {N S : ℕ} (F : GraphParameters N) (P : CountLaw F.d)
    (A : Estimator (N+N) S) (mode : Arrival) (p : ℕ) : ℝ :=
  ∑ B : NeighborLists N, (graphLaw N F.h F.d P B).toReal *
    ((A.law p (hardColor N) (hardStream mode B)) (Set.Ioi ((N : ℝ)/(8*F.c)))).toReal

def graphTestGap {N S : ℕ} (F : GraphParameters N)
    (A : Estimator (N+N) S) (mode : Arrival) (p : ℕ) : ℝ :=
  |graphAcceptance F F.P₁ A mode p - graphAcceptance F F.P₀ A mode p|

end
end CoarseMatching.LowerBound


