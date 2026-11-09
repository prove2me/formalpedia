-- Prove2me | Definitions.Def_HybridXorLift_badProb
-- name    : HybridXorLift_badProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:25:20.079375+00:00
-- url     : https://prove2.me/theorems/bea85d65-1c97-4b42-84af-4fc519354a1e
-- title:
--   Probability $B_z$ of reaching a bad history
-- statement:
--   Fix an outer string $z$ and $\eta = 1/(1000(n+1))$ (5.5). The true process draws $x$ uniformly from $\sigma^{-1}(z)$ and runs the hybrid algorithm, so it reaches a history $h$ with probability $\ell_h(z)$. $B_z$ is the probability that the true process reaches a history that is bad for $z$:
--   $$
--   B_z = \sum_{\lambda \text{ terminal},\ \exists\, v \preceq \lambda \text{ bad for } z} \ell_\lambda(z),
--   $$
--   the sum over the terminal histories some prefix of which (possibly $\lambda$ itself) is bad.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §5.2, p.18 (PDF p.20); Eq. (5.5)

import Definitions.Def_HybridXorLift_IsGood
import Definitions.Def_HybridXorLift_ParallelHybridAlg_terminals

namespace HybridXorLift

open Classical in
/-- `B_z`, the probability that the true process reaches a bad history (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §5.2, p.18 (PDF
p.20)): the true process draws `x` uniformly from `σ⁻¹(z)` and runs the algorithm, so it ends at
the terminal history `λ` with probability `ℓ_λ(z)`, and it reaches a bad history exactly when
some prefix of `λ` (including `λ` itself) is bad for `z`. Goodness is taken with
`η = 1/(1000(n + 1))` (Eq. (5.5), p.18 (PDF p.20)). -/
noncomputable def badProb {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α) (q : ℕ)
    (z : Fin n → Bool) : ℝ :=
  ∑ l ∈ A.terminals.filter (fun l => ∃ t ≤ l.length,
      ¬ IsGood A q (1 / (1000 * ((n : ℝ) + 1))) z (l.take t)), likelihood A l z

end HybridXorLift


