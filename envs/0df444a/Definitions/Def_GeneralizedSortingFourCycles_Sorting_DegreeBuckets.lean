-- Prove2me | Definitions.Def_GeneralizedSortingFourCycles_Sorting_DegreeBuckets
-- name    : GeneralizedSortingFourCycles_Sorting_DegreeBuckets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:52.256183+00:00
-- url     : https://prove2.me/theorems/b6f0213c-4b78-42d0-bbf5-ab217410f715
-- title:
--   Entry degrees and dyadic vertex buckets
-- statement:
--   Let $H$ be the graph of active edges at entry to a call, and write $d(v)$ for its degree and $m$ for its number of undirected edges. Retaining $H$ freezes these entry quantities even when later queries certify edges. Set $B_i=2^i$ and
--   $$V_i=\{v:B_i/2<d(v)\le B_i\}.$$
--   Degree-zero vertices belong to no bucket. The finite range $0\le i\le\lfloor\log_2 n\rfloor+1$ covers all positive degrees, including degrees above $2^{\lfloor\log_2 n\rfloor}$; unused buckets are empty. For sufficiently large $n$ its length is at most $2\ln n$, as required by the paper. The logarithm in resource bounds remains natural; the integer binary logarithm is used solely to enumerate dyadic buckets.
-- source:
--   Soheil Behnezhad, Shane Ferrante, STOC 2027 submission #1354 (October 2026), Algorithms 1–2, printed pp. 7–8 (PDF pp. 8–9); Claim 2, printed p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1354.pdf

import Mathlib

namespace GeneralizedSortingFourCycles.Sorting

/-- Number of active neighbours, frozen by retaining the entry graph H. -/
noncomputable def entryDegree {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun u => H.Adj v u).card

/-- Each undirected active edge is counted once. -/
noncomputable def activeEdgeCount {n : ℕ} (H : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ H.Adj p.1 p.2).card

/-- A finite integer range covering every positive degree up to n-1.
The extra top index covers degrees above 2^(floor(log2 n)); unused buckets are empty.
The source's 2 ln n is an asymptotic upper bound on the number of buckets. -/
def bucketCount (n : ℕ) : ℕ := n.log2 + 2

def bucketUpper (i : ℕ) : ℕ := 2 ^ i

/-- Entry degrees, with the source's strict lower and weak upper inequalities.
Degree-zero vertices belong to no bucket and require no active-edge processing. -/
noncomputable def degreeBucket {n : ℕ} (H : SimpleGraph (Fin n)) (i : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v =>
    (bucketUpper i : ℝ) / 2 < (entryDegree H v : ℝ) ∧ entryDegree H v ≤ bucketUpper i

end GeneralizedSortingFourCycles.Sorting


