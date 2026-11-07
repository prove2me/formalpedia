-- Prove2me | Definitions.Def_AvgPHETH_IsRespFamily
-- name    : AvgPHETH_IsRespFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:04.113955+00:00
-- url     : https://prove2.me/theorems/c6fc1e0a-2d04-4ff4-ab8c-ea960beceef7
-- title:
--   A uniformly computable family $f_n(z,q)\in\{0,1\}^{\ell(n)}$
-- statement:
--   The family $f_n(z,q)\in\{0,1\}^{\ell(n)}$ is computed by the given machine with the given oracle, uniformly in $n$, $z\in\{0,1\}^{\le r(n)}$ and $q\in\{0,1\}^{m(n)}$, with running time at most $\mathrm{time}_f(n,|z|)$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §5.1, p.20 (PDF 22); Lemma 5.1, p.19 (PDF 21)

import Mathlib
import Definitions.Def_AvgPHETH_resp
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
open KarpLiptonOM

namespace AvgPHETH

/-- The family `f_n(z, q) ∈ {0,1}^{ℓ(n)}` of §5 is computed by the machine `M` with oracle `P`, uniformly in
`n`, `z ∈ {0,1}^{≤ r(n)}` and `q ∈ {0,1}^{m(n)}`, with running time at most `time_f(n, |z|)`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §5.1, p.20 (PDF 22); Lemma 5.1, p.19 (PDF 21)). -/
def IsRespFamily (M : OracleTM) (P : Set (List Bool)) (timef : ℕ → ℕ → ℕ) (m ℓ : ℕ → ℕ)
    (r : Polynomial ℕ) : Prop :=
  ∀ (n : ℕ) (z q : List Bool), z.length ≤ r.eval n → q.length = m n →
    M.HaltsWithin P (timef n z.length) (tupleEnc [unary n, z, q]) ∧
      (resp M P timef n z q).length = ℓ n

end AvgPHETH


