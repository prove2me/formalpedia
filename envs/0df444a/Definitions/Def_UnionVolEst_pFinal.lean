-- Prove2me | Definitions.Def_UnionVolEst_pFinal
-- name    : UnionVolEst_pFinal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:58.133612+00:00
-- url     : https://prove2.me/theorems/c3922e96-8c76-4b0e-8b04-c9bfda33db3a
-- title:
--   Final sampling intensity $p_{\mathrm{final}}$
-- statement:
--   $p_{\mathrm{final}}$ is the sampling intensity $p=2^{-\ell}$ at the end of a run.
--
--   **Formalization Note** For a run that never terminates it is set to $0$, so such runs belong to $\mathrm{Fail}_{\mathrm{prob}}=\{p_{\mathrm{final}}<1/F_0\}$.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_UnionVolEst_AlponaState

namespace UnionVolEst

/-- The final sampling intensity `p_final = 2^{−level}` of a run (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, printed p.18,
PDF p.20).

**Formalization Note** On a run that never terminates (`none`) it is `0`, so such runs lie in
`Fail_prob = {p_final < 1/F₀}`. -/
noncomputable def pFinal {n : ℕ} : Option (AlponaState n) → ℝ
  | some s => ((2 : ℝ)⁻¹) ^ s.level
  | none => 0

end UnionVolEst


