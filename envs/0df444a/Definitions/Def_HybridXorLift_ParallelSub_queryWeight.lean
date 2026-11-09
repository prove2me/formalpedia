-- Prove2me | Definitions.Def_HybridXorLift_ParallelSub_queryWeight
-- name    : HybridXorLift_ParallelSub_queryWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:48.507212+00:00
-- url     : https://prove2.me/theorems/4188616f-8e2d-4c51-9449-7a4fd14f946c
-- title:
--   Query weight $\beta_i$ of a parallel subroutine
-- statement:
--   Resolve the prepared state $|\phi\rangle$ of a parallel subroutine into the orthogonal sectors on which all slot labels are fixed, and let $\mu(a)$ be the squared norm of the component with label tuple $a = (a_1,\dots,a_k)$, summed over the workspace; $\mu$ is an input-independent probability distribution. A slot labelled by a physical address $(i, j)$ and a control bit is **active** when the control bit is $1$. The **query weight** of block $i$ is
--   $$
--   \beta_i = \mathbb E_{a \sim \mu} \big[\text{number of active slots of } a \text{ addressing block } i\big].
--   $$
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.1, Eq. (4.1), p.14 (PDF p.16)

import Definitions.Def_HybridXorLift_ParallelSub

namespace HybridXorLift

/-- The query weight `β_i = E_{a ∼ μ} [number of active slots of a addressing block i]` of block
`i` in a parallel subroutine (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.1, Eq. (4.1), p.14 (PDF p.16)), where `μ(a)` is the
squared norm of the component of the prepared state `|ϕ⟩` with slot labels `a`, summed over the
workspace. A slot with label `((i, j), b)` addresses block `i`, and it is active when its
control bit `b` is `1`. -/
noncomputable def ParallelSub.queryWeight {n r k w : ℕ} (S : ParallelSub (Fin n × Fin r) k w)
    (i : Fin n) : ℝ :=
  ∑ a : Fin k → (Fin n × Fin r) × Bool, (∑ v : Fin w, ‖S.start (a, v)‖ ^ 2) *
    ((Finset.univ.filter fun l => (a l).2 = true ∧ (a l).1.1 = i).card : ℝ)

end HybridXorLift


