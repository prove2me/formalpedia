-- Prove2me | Definitions.Def_AvgPHETH_resp
-- name    : AvgPHETH_resp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:37.238998+00:00
-- url     : https://prove2.me/theorems/6286fc5c-4342-4ea5-b92f-8af9ecd91c0f
-- title:
--   The response $f_n(z,q)$
-- statement:
--   The response $f_n(z,q)$ of Section 5: the output of one fixed machine with the given oracle on input $(1^n,z,q)$ after $\mathrm{time}_f(n,|z|)$ steps.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §5.1, p.20 (PDF 22)

import Mathlib
import Definitions.Def_AvgPHETH_outAt
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_unary
open KarpLiptonOM

namespace AvgPHETH

/-- The response `f_n(z, q)` of §5: the output of one machine `M` with oracle `P` on `(1^n, z, q)` after
`time_f(n, |z|)` steps (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §5.1, p.20 (PDF 22)). -/
noncomputable def resp (M : OracleTM) (P : Set (List Bool)) (timef : ℕ → ℕ → ℕ) (n : ℕ)
    (z q : List Bool) : List Bool :=
  outAt M P (timef n z.length) (tupleEnc [unary n, z, q])

end AvgPHETH


