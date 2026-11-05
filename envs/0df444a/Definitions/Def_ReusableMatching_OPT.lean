-- Prove2me | Definitions.Def_ReusableMatching_OPT
-- name    : ReusableMatching_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:12.303361+00:00
-- url     : https://prove2.me/theorems/9c18ed3a-0433-420e-9f47-4056c330ab7a
-- title:
--   The optimal offline reward OPT
-- statement:
--   For an OBMRR instance with weights $r_i\ge0$, the **optimal offline reward** is
--
--   $$
--   \mathrm{OPT}=\max\Big\{\sum_{(i,j)\in M} r_i \;:\; M \text{ a feasible reusable matching}\Big\}.
--   $$
--
--   It is the value of the best matching chosen by an offline algorithm that knows the whole graph in advance. Competitive ratios compare the expected reward of an online algorithm with $\mathrm{OPT}$.
--
--   **Formalization Note** The maximum is finite, taken over the subsets of the finite edge set; the empty matching is feasible, so the family is nonempty. This is the integral optimum, not the value of the LP relaxation of §2.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, p.2 (optimal offline algorithm), p.3 ("maximize the total accumulated weight")

import Mathlib
import Definitions.Def_ReusableMatching_IsFeasibleMatching

namespace ReusableMatching

/-- **The optimal offline reward** `OPT` of an OBMRR instance (arXiv:2110.07084v2, p.2: "we compare
our algorithm to the optimal offline algorithm that has the complete knowledge of `G`"; p.3: "The
goal of both the online algorithm and the optimum offline solution is to maximize the total
accumulated weight from matching online nodes"):
`OPT = max { ∑_{(i, j) ∈ M} r_i : M a feasible reusable matching }`.

**Formalization Note.** The maximum is a finite one, taken over the subsets of the finite edge set
`E` that satisfy `IsFeasibleMatching`. The empty matching is feasible, so the family is nonempty
and no junk value of a real supremum occurs. This is the integral offline optimum, not the value of
the LP relaxation of §2 (p.6). -/
noncomputable def OPT {V : Type*} {n : ℕ} (I : OBMRRInstance V n) : ℝ := by
  classical
  exact (I.E.powerset.filter (IsFeasibleMatching I)).sup'
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _,
      ⟨Finset.empty_subset _, by simp, by simp⟩⟩⟩
    (fun M => ∑ p ∈ M, I.r p.1)

end ReusableMatching


