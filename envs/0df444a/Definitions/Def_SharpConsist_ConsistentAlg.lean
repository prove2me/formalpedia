-- Prove2me | Definitions.Def_SharpConsist_ConsistentAlg
-- name    : SharpConsist_ConsistentAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:19.534871+00:00
-- url     : https://prove2.me/theorems/ffa3d56e-7810-47fe-90d5-0ef6c2f18f6d
-- title:
--   Randomized value-oracle algorithm on the stream $1,\dots,n,r$
-- statement:
--   A **randomized value-oracle algorithm** on the stream $1,\dots,n,r$ is described at the two times the lower bound uses: just before the final arrival (output $S^-=S_n\subseteq X$) and just after it (output $S^+=S_{n+1}\subseteq X\cup\{r\}$). Its randomness is a seed $\omega$ drawn from an arbitrary seed space $\Omega$. For each seed:
--
--   1. before $r$ arrives, the algorithm is a deterministic adaptive rule making $Q$ value queries on subsets of $X$, each query depending on all earlier answers, followed by an output $S^-(\omega)\subseteq X$ computed from the answers; it sees the objective only through these answers;
--   2. after $r$ arrives, it outputs $S^+(\omega)\subseteq X\cup\{r\}$ with full access to the objective $f$.
--
--   This class contains every algorithm of the paper's model run on this stream: the paper's queries before the last arrival lie in the arrived history, adaptive and unrestricted in computation, and its queries and computation after the last arrival are unrestricted.
--
--   **Formalization Note.** The pre-arrival rule is the published `NonmonotoneSubmod.QueryLB.DetAlg (Fin n) Q`. All pre-arrival queries form one rule with $Q$ slots, which also knows $n$; an algorithm making fewer queries pads with dummy ones, and the finite rule builds in termination.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1, p.1; §2.1, p.4; Theorem 1.1(ii), p.2; Theorem 5.1, p.12

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm
import Definitions.Def_SharpConsist_embedX

universe u

namespace SharpConsist

/-- A **randomized value-oracle algorithm on the stream `1, 2, …, n, r`**, seen at the two times that
matter for the lower bound: just before the final arrival `r` (output `S⁻ = S_n`) and just after it
(output `S⁺ = S_{n+1}`). Fu–Zhang–Tao, arXiv:2609.09986 (held version, sha256 874ec76c…), §1, p.1;
§2.1, p.4; Theorem 1.1(ii), p.2; Theorem 5.1, p.12.

The randomness is a seed `ω` of an arbitrary seed space `Ω`. For each seed,
* `pre ω` is a deterministic adaptive query rule with `Q` query slots on subsets of the current set
  `X = Fin n` (`NonmonotoneSubmod.QueryLB.DetAlg`): each query may depend on all earlier answers, and
  its output is `S⁻ ⊆ X`;
* `post ω f` is the output `S⁺ ⊆ X ∪ {r}` after the final arrival, computed with full access to `f`
  ("Queries and computation after the final arrival are unrestricted", p.12).

**Formalization Note.** (a) All queries before `r` are collapsed into one adaptive rule over all
subsets of `X` with a total budget of `Q` queries; every online algorithm whose queries at time `t`
lie in `X_t` gives such a rule, so this class is larger than the paper's. (b) The rule knows `n` and the
arrival order. (c) The budget is exactly `Q` query slots: an algorithm that stops earlier pads with
dummy queries, and finiteness builds in termination (a run that fails to terminate on a null set of
seeds is changed there, which changes no expectation). (d) `post` may use `f` in full, including
the hidden set. -/
structure ConsistentAlg (n Q : ℕ) (Ω : Type u) where
  /-- The query rule used before the final arrival, for each seed. -/
  pre : Ω → NonmonotoneSubmod.QueryLB.DetAlg (Fin n) Q
  /-- The output after the final arrival, for each seed and objective. -/
  post : Ω → (Finset (Fin (n + 1)) → ℝ) → Finset (Fin (n + 1))

/-- The output `S⁻ = S_n ⊆ X` just before the final arrival: the query rule of seed `ω` run against
the oracle of `f` restricted to subsets of `X`. The pre-arrival phase sees `f` only through these
answers. -/
def ConsistentAlg.preOut {n Q : ℕ} {Ω : Type u} (alg : ConsistentAlg n Q Ω) (ω : Ω)
    (f : Finset (Fin (n + 1)) → ℝ) : Finset (Fin n) :=
  (alg.pre ω).run (restrictX f)

end SharpConsist


