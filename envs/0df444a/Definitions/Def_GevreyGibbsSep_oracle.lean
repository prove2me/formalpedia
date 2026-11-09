-- Prove2me | Definitions.Def_GevreyGibbsSep_oracle
-- name    : GevreyGibbsSep_oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:47.27508+00:00
-- url     : https://prove2.me/theorems/79b2daed-6427-4746-8298-26a796f33054
-- title:
--   Definition B.2 — oracle of order $k$
-- statement:
--   Let $k\in\mathbb N\cup\{\infty\}$. Queried at $x\in\mathbb T^d$ on the instance $p=e^{-V}/Z_V$, the **oracle of order $k$** answers with the value and all derivatives up to order $k$ of the log-density,
--   $$\phi_k(p,x)=\big(\nabla^{\otimes j}\log\bar p(x)\big)_{j=0}^{k},\qquad \log\bar p=-V-\log Z_V .$$
--   The order-zero entry is $-\beta E(x)-\log Z$, which evaluation of the potential alone need not supply. $k=0$ is the evaluation oracle, $k=1$ the gradient (score) oracle.
--
--   **Formalization Note** $k$ ranges over $\mathbb N\cup\{\infty\}$; entries above order $k$ are reported as $0$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.2, Eq. (B2), p.34; Eq. (9), p.6

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_iterPartial
import Definitions.Def_GevreyGibbsSep_partitionFn
import Definitions.Def_GevreyGibbsSep_Answer
import Definitions.Def_GevreyGibbsSep_torusRep

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition B.2 (oracle of order `k`), arXiv:2608.24527 (sha256 d4fd40eb…), Eq. (B2), p.34
(and Eq. (9), p.6): queried at `x ∈ T^d` on the instance with potential `V`, it returns
`ϕ_k(p, x) = (∇^{⊗j} log p̄(x))_{j=0}^{k}`, where `log p̄ = −V − log Z_V`.

**Formalization Note** `k : ℕ∞` (`k = ⊤` is the order-∞ oracle). Entries of order `j > k` are
`0`. The order-0 entry is `−V(x) − log Z_V` (the log-density), not `−V(x)`. -/
noncomputable def oracle {d : ℕ} (k : ℕ∞) (V : (Fin d → ℝ) → ℝ) (x : Torus d) : Answer d :=
  fun j idx => if (j : ℕ∞) ≤ k then
    iterPartial (List.ofFn idx) (fun y => - V y - Real.log (partitionFn V)) (torusRep x) else 0

end GevreyGibbsSep


