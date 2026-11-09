-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Offline
-- name    : MLAMaxDelay_RandomizedTimer_Offline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:18.606205+00:00
-- url     : https://prove2.me/theorems/9b28cc95-31ba-4fce-bce9-ceffd4fd678f
-- title:
--   Arrival epochs and the two-output offline dynamic program
-- statement:
--   The distinct arrival times are sorted, with all occurrences at each time retained together. $C(i,j)$ is the rooted footprint weight of the epochs in an interval, and $D(i,j)$ is its actual offline schedule optimum. Algorithm 1 constructs the table
--   $$F(j)=\min_{p<j}\{F(p)+C(p,j)+a_{j-1}-a_p\},\qquad F(0)=0$$
--   in zero-based half-open notation. Each row stores its minimizing predecessor and the predecessor schedule followed by the chosen terminal service. The output contains both the value and the recovered schedule. This is a concrete computation from earlier rows; neither $D$ nor the true offline optimum is defined by this recurrence.
--
--   **Formalization Note.** The smallest minimizing prefix length is selected. Cached recovered prefixes implement the same predecessor backtracking, without asserting the source running-time bound.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 4–7, Algorithm 1 and equations (1)–(2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Model

namespace MLAMaxDelay.RandomizedTimer

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Distinct arrival epochs sorted in increasing order. Indices are zero-based. -/
noncomputable def epochs (I : Input V) : List ℝ :=
  (I.requests.image I.arrival).sort (· ≤ ·)

noncomputable def epochTime (I : Input V) (i : ℕ) : ℝ :=
  (epochs I)[i]?.getD 0

/-- Source [i,j] becomes [i-1,j) here. Empty half-open intervals give the empty input. -/
noncomputable def intervalRequests (I : Input V) (i j : ℕ) : Finset ℕ := by
  classical
  exact I.requests.filter (fun r => I.arrival r ∈ ((epochs I).drop i |>.take (j-i)))

noncomputable def intervalC (T : WeightedTree V) (I : Input V) (i j : ℕ) : ℝ :=
  kappa T I (intervalRequests I i j)

noncomputable def intervalD (T : WeightedTree V) (I : Input V) (i j : ℕ) : ℝ :=
  optimumReal T (restrictInput I (intervalRequests I i j))

/-- A DP entry stores its value, predecessor and recovered schedule. Keeping the
recovered prefix here is equivalent to backtracking the stored predecessor table. -/
structure DPEntry (V : Type) where
  value : ℝ
  predecessor : ℕ
  schedule : Schedule V

noncomputable def entryAt (tab : List (DPEntry V)) (p : ℕ) : DPEntry V :=
  tab[p]?.getD ⟨0, 0, []⟩

noncomputable def dpCandidate (T : WeightedTree V) (I : Input V)
    (tab : List (DPEntry V)) (j p : ℕ) : ℝ :=
  (entryAt tab p).value + intervalC T I p j + epochTime I (j-1) - epochTime I p

/-- A finite argmin; ties choose the smallest prefix length. The domain is [0,j). -/
noncomputable def bestPredecessor (T : WeightedTree V) (I : Input V)
    (tab : List (DPEntry V)) (j : ℕ) : ℕ :=
  ((List.range j).foldl (fun best p =>
    if dpCandidate T I tab j p < dpCandidate T I tab j best then p else best) 0)

/-- Algorithm 1, pp. 4–5. The next row reads only earlier rows. -/
noncomputable def dpTable (T : WeightedTree V) (I : Input V) : ℕ → List (DPEntry V)
  | 0 => [⟨0, 0, []⟩]
  | j+1 =>
    let tab := dpTable T I j
    let p := bestPredecessor T I tab (j+1)
    tab ++ [⟨dpCandidate T I tab (j+1) p, p,
      (entryAt tab p).schedule ++
        [(epochTime I j, footprint T I (intervalRequests I p (j+1))) ]⟩]

noncomputable def offlineAlgorithm (T : WeightedTree V) (I : Input V) : DPEntry V :=
  entryAt (dpTable T I (epochs I).length) (epochs I).length

noncomputable def finiteMinimum (i j : ℕ) (f : ℕ → ℝ) : ℝ :=
  if h : (Finset.Ico i j).Nonempty then
    ((Finset.Ico i j).image f).min' (h.image f) else 0

end MLAMaxDelay.RandomizedTimer


