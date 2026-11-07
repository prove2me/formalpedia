-- Prove2me | Definitions.Def_KarpLiptonOM_promiseJoin
-- name    : KarpLiptonOM_promiseJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:59.82879+00:00
-- url     : https://prove2.me/theorems/c2ebf4e4-af66-4a9a-829c-56fd14603ffa
-- title:
--   Join $\Pi_1 \oplus \cdots \oplus \Pi_r$ of promise problems
-- statement:
--   For promise problems $\Pi_1, \dots, \Pi_r$, the **join** $\Pi_1 \oplus \cdots \oplus \Pi_r$ is the promise problem with
--   $$
--   \text{yes-instances } \langle i, q\rangle \ (q \in (\Pi_i)_{\mathrm{YES}}), \qquad \text{no-instances } \langle i, q\rangle \ (q \in (\Pi_i)_{\mathrm{NO}}),
--   $$
--   where $\langle i, q\rangle$ is $q$ preceded by a fixed-width code of $i$. A language consistent with the join yields, by restriction, a language consistent with each $\Pi_i$; one oracle for the join replaces $r$ separate oracles.
--
--   **Formalization Note** Indices run over $\{0, \dots, r-1\}$ and $\langle i, q\rangle$ is the one-hot tag of $i$ followed by $q$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21 (after Definition A.2.1)

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_KarpLiptonOM_joinTag

namespace KarpLiptonOM

/-- The join `Π₁ ⊕ ⋯ ⊕ Π_r` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21): yes-instances `⟨i, q⟩` for `q ∈ (Π_i)_YES` and
no-instances `⟨i, q⟩` for `q ∈ (Π_i)_NO`, with `⟨i, q⟩ = joinTag r i ++ q`. The disjointness proof is
structural (tags of equal width are distinct for distinct indices). -/
def promiseJoin {r : ℕ} (PP : Fin r → PromiseProblem) : PromiseProblem where
  yes := {s | ∃ i q, q ∈ (PP i).yes ∧ s = joinTag r i ++ q}
  no := {s | ∃ i q, q ∈ (PP i).no ∧ s = joinTag r i ++ q}
  disjoint := by
    rw [Set.disjoint_left]
    rintro s ⟨i, q, hq, rfl⟩ ⟨j, q', hq', h⟩
    have hlen : (joinTag r i).length = (joinTag r j).length := by simp [joinTag]
    obtain ⟨h1, h2⟩ := List.append_inj h hlen
    have hij : i = j := by
      have h3 := congrFun (List.ofFn_inj.mp h1) i
      simpa using h3.symm
    subst hij; subst h2
    exact Set.disjoint_left.mp (PP i).disjoint hq hq'

end KarpLiptonOM


