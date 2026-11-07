-- Prove2me | Definitions.Def_KServerConj_opt
-- name    : KServerConj_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:58.472217+00:00
-- url     : https://prove2.me/theorems/80801a46-cb14-4786-8d23-66e15a37c21c
-- title:
--   Optimal offline cost $\mathrm{OPT}_{C_0}(r_1,\dots,r_T)$
-- statement:
--   With the notation of the work function, the **optimal offline cost** of the requests $r_1,\dots,r_T$ from the initial configuration $C_0$ is
--
--   $$\mathrm{OPT}_{C_0}(r_1,\dots,r_T)=\inf\Big\{\sum_{s=1}^T D(S_{s-1},S_s)\ :\ S\ \text{an offline schedule serving } r_1,\dots,r_T\Big\},$$
--
--   the least total movement cost of $k$ servers that start at $C_0$ and are at $r_s$ at time $s$ for every $s$. The paper writes it as $\mathrm{OPT}_{C_0}(r_1,\dots,r_T)=\min_X w_T(X)$.
--
--   **Formalization Note** Defined directly from offline schedules, so that its identity with $\min_X w_T(X)$ is a fact rather than a definition. The set is nonempty for $k\ge1$, $|C_0|=k$, and bounded below by $0$.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_KServerConj_workFn

namespace KServerConj

/-- **The optimal offline cost** `OPT_{C₀}(r₁, …, r_T)`, Coester, Koutsoupias, Zbysiński,
*The k-server conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…),
§1.1, printed p.2 (PDF p.3): the minimum total movement cost of an offline schedule serving the
requests `r 1, …, r T` from the initial configuration `C₀`; the paper writes it as
`OPT_{C₀}(r₁, …, r_T) = min_X w_T(X)`.

**Formalization Note.** `opt k C₀ r T` is the infimum over offline schedules (`IsSchedule`) of
`∑_{s=1}^T D(S (s-1), S s)`; the identity with `min_X w_T(X)` is then a fact, not a definition.
The set is nonempty for `1 ≤ k` and `C₀.card = k`, and bounded below by `0`. -/
noncomputable def opt {M : Type*} [PseudoMetricSpace M] (k : ℕ) (C₀ : Finset M) (r : ℕ → M)
    (T : ℕ) : ℝ :=
  sInf {c | ∃ S : ℕ → Finset M, IsSchedule k C₀ r T S ∧
    c = ∑ s ∈ Finset.Icc 1 T, confDist (S (s - 1)) (S s)}

end KServerConj


