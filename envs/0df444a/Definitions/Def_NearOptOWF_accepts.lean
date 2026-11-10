-- Prove2me | Definitions.Def_NearOptOWF_accepts
-- name    : NearOptOWF_accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:39.716617+00:00
-- url     : https://prove2.me/theorems/bfb29102-c16d-4670-8097-c0fd6e910266
-- title:
--   Acceptance of a distinguisher circuit
-- statement:
--   For a distinguisher circuit $D$ with $k$ inputs and a string $s$, $\mathrm{acc}_D(s) \in \{0,1\}$ is $1$ exactly when the first output bit of $D$ on $s$ is $1$. The string is fed to $D$ as $s10\cdots0$, cut or padded to length $k$. Averaged over the coins that produce $s$, it is the probability $\Pr[D(s) = 1]$ that appears in every security definition of the mission.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- The indicator that a (non-uniform) distinguisher circuit `D` with `k` inputs outputs `1` on the
string `s` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4, p.9 (PDF p.11): "`Pr[D(iO(C₀)) = 1]`"): `D` reads `s` through
`padIn k` (the string `s10⋯0` cut or padded to length `k`) and its output is its first output bit.

**Formalization Note** The value is `1` or `0`; averaged over coins (`LaconicBarrier.coinAvg`) it is
the acceptance probability. A circuit without outputs rejects. -/
noncomputable def accepts {k : ℕ} (D : MCircuit k) (s : List Bool) : ℝ :=
  if (D.eval (padIn k s)).headD false = true then 1 else 0

end NearOptOWF


