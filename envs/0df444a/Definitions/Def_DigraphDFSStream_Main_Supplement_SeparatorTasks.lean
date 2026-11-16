-- Prove2me | Definitions.Def_DigraphDFSStream_Main_Supplement_SeparatorTasks
-- name    : DigraphDFSStream_Main_Supplement_SeparatorTasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:56:58.898347+00:00
-- url     : https://prove2.me/theorems/f24a9d78-f31c-4102-820a-7e030297766f
-- title:
--   Streaming output tasks for multipath and cycle separators
-- statement:
--   A multipath output is a family of disjoint nonempty simple directed paths whose deletion leaves every strongly connected component of the input graph with at most half the input's vertices, together with an upper bound on the number of paths. A merge output replaces two selected paths by a family of size at most one and keeps the entire ordered list of unselected paths unchanged. A cycle output is a list in cyclic vertex order satisfying the published cycle-separator predicate; a singleton requires no self-loop.
--
--   All separator tests use the input graph's fixed balance threshold $n/2$. They do not rebalance against the size of a smaller induced graph. A cycle program's high-probability specification uses the actual success event and the same confidence convention as the published DFS target:
--   $$\Pr(\text{valid cycle separator})\ge1-n^{-(c+1)}\quad(n\ge2).$$
--   At $n=1$ correctness is exact; at $n=0$ no cycle correctness is asserted. The published all-tape bit and pass bounds still cover size zero. The subpower target requires one program and one pass function for each confidence level, with that same function bounded by $O(n^{3/4+\varepsilon})$ for every $\varepsilon>0$. The quarter-power specialization supplies exactly $k=\lceil n^{1/4}\rceil$ through the charged task header.
--
--   These are output and execution predicates, not assumed correctness contracts for a guessed algorithm. Existence of programs satisfying them is asserted by the theorem items.
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Definition 2.2, printed p.4 (PDF p.5); Lemmas 4.5–4.8 and Proposition 4.1, printed pp.12–17 (PDF pp.13–18); Theorem 1.2, printed p.2 (PDF p.3)

import Definitions.Def_DigraphDFSStream_Main_Supplement_PrimitiveTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

def MultipathOutput {n : ℕ} (E : Finset (Fin n × Fin n)) (maxPaths : ℕ)
    (out : List Bool) : Prop :=
  ∃ Q : List (List (Fin n)), out = familyCode Q ∧
    IsMultipathSeparator E Finset.univ Q ∧ Q.length ≤ maxPaths

/-- The entire list of other paths is retained unchanged, in its original order. -/
def MergeOutput {n : ℕ} (E : Finset (Fin n × Fin n))
    (others : List (List (Fin n))) (out : List Bool) : Prop :=
  ∃ Q : List (List (Fin n)), Q.length ≤ 1 ∧ out = familyCode (Q ++ others) ∧
    IsMultipathSeparator E Finset.univ (Q ++ others)

def CycleOutput {n : ℕ} (E : Finset (Fin n × Fin n)) (out : List Bool) : Prop :=
  ∃ Z : List (Fin n), out = vertexCode Z ∧ IsCycleSeparator E Finset.univ Z

def CycleSuccess {n : ℕ} (P : StreamProgram) (input : List (Fin n × Fin n)) :
    Set (ℕ → Bool) :=
  {ω | ∃ out, StreamHalts P input ω out ∧ CycleOutput input.toFinset out}

/-- No correctness requirement at n=0: there is no nonempty cycle or singleton there.
All-tape resource bounds still include n=0, using the published HasStreamingBounds. -/
def CycleHighProbability (P : StreamProgram) (c : ℕ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ input : List (Fin n × Fin n),
    MeasurableSet (CycleSuccess P input) ∧
      1 - failure c n ≤ fairCoins.real (CycleSuccess P input)

def CycleSubpower : Prop :=
  ∀ c : ℕ, ∃ (P : StreamProgram) (bits passes : ℕ → ℕ),
    SemistreamingBits bits ∧ SubpowerPasses (3 / 4 : ℝ) passes ∧
      HasStreamingBounds P bits passes ∧ CycleHighProbability P c

/-- The specialization keeps one algorithm and one pass function for every epsilon,
and supplies exactly k=ceil(n^(1/4)) as the task's charged integer parameter. -/
def QuarterSpecialization : Prop :=
  ∀ c : ℕ, ∃ (P : StreamProgram) (bits passes : ℕ → ℕ),
    SemistreamingBits bits ∧ SubpowerPasses (3 / 4 : ℝ) passes ∧
      ∀ n : ℕ, 1 ≤ n → ∀ input : List (Fin n × Fin n),
        Solves P input (natCode (quarterK n)) (CycleOutput input.toFinset)
          (bits n) (passes n) c n

end DigraphDFSStream.Main.Supplement


