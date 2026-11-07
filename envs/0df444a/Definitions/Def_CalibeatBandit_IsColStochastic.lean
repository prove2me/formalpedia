-- Prove2me | Definitions.Def_CalibeatBandit_IsColStochastic
-- name    : CalibeatBandit_IsColStochastic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:15.579208+00:00
-- url     : https://prove2.me/theorems/f2731dc9-a91b-4f58-851c-6d6081683458
-- title:
--   Column-stochastic $K\times K$ matrices
-- statement:
--   A real $K\times K$ matrix $M$ is **column-stochastic** if each of its columns $M_{\cdot i}=(M_{ji})_{j\in\mathcal A}$ is a probability vector on $\mathcal A$.
--
--   The post-processing matrix $M^a_t=[m^a_{t,1}\mid\cdots\mid m^a_{t,K}]$ of the internal learners has the post-processing distribution $m^a_{t,i}$ of action $i$ as its $i$-th column, and $(M^a_t)_{ji}$ is the probability of post-processing action $i$ into action $j$; it is column-stochastic.
--
--   **Formalization Note** `M j i` is the entry in row $j$, column $i$.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §3 (Internal learners), p.9 (PDF 9)

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec

set_option autoImplicit false

namespace CalibeatBandit

/-- **Column-stochastic matrix.** A `K × K` real matrix `M` is column-stochastic when each of
its columns `M · i = (M j i)_j` is a probability vector on `[K]`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §3 "Internal
learners", p.9: the post-processing matrix `M^a_t = [m^a_{t,1} | ⋯ | m^a_{t,K}]` has the mixed
strategy `m^a_{t,i} ∈ Δ(𝒜)` as its column `i`, and "(M^a_t)_{ji} is the probability of
post-processing action i into action j. Observe that M^a_t is column-stochastic."

**Formalization Note.** `M j i` is the entry in row `j`, column `i`. -/
def IsColStochastic {K : ℕ} (M : Matrix (Fin K) (Fin K) ℝ) : Prop :=
  ∀ i, IsProbVec (fun j => M j i)

end CalibeatBandit


