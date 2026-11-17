-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_noisyReps
-- name    : NoPerfectRandComp_Supplement_noisyReps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:19:45.533193+00:00
-- url     : https://prove2.me/theorems/463a5501-ff9c-4553-9098-25065d33e759
-- title:
--   Noisy randomized query complexity $\mathrm{noisyR}_\epsilon$
-- statement:
--   For a possibly partial Boolean function $f$ and $\epsilon\ge 0$,
--   $$
--   \mathrm{noisyR}_\epsilon(f) = \inf_A\ \max_{x\in\mathrm{Dom}(f)}\ \mathbb E[\mathrm{cost}(A,x)],
--   $$
--   the infimum over noisy algorithms $A$ with error $\Pr[A(x)\ne f(x)]\le\epsilon$ at every $x\in\mathrm{Dom}(f)$. The paper's $\mathrm{noisyR}(f)$ is $\mathrm{noisyR}_{1/3}(f)$: worst-input expected total cost and error at most $1/3$.
--
--   **Formalization Note** Valued in $[0,\infty]$. The error condition is $\Pr[A \text{ halts with output } f(x)]\ge 1-\epsilon$, so a run that never halts counts as an error. The same module defines the abbreviation `noisyR` for $\epsilon = 1/3$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4, p.11; Theorem 10.3, p.51

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_NoPerfectRandComp_Supplement_noisyOut
import Definitions.Def_NoPerfectRandComp_Supplement_noisyCost
open scoped ENNReal

namespace NoPerfectRandComp

namespace Supplement

/-- Noisy randomized query complexity at error `ε` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4, p.11; used at small `ε` in
Theorem 10.3, p.51): the least worst-input expected total cost of a noisy algorithm whose error
`err(A, x) = Pr[A(x) ≠ f(x)]` is at most `ε` at every `x ∈ Dom(f)`:
`noisyR_ε(f) = inf_A sup_{x ∈ Dom(f)} E[cost(A, x)]`.

**Formalization Note** Valued in `ℝ≥0∞`. The error condition is
`Pr[A halts with output f(x)] ≥ 1 − ε`, so a run that does not halt counts as an error. -/
noncomputable def noisyReps {ι : Type} (ε : ℝ) (f : PartialFn ι) : ℝ≥0∞ :=
  ⨅ (A : NoisyAlg ι) (_ : ∀ x ∈ f.dom, ENNReal.ofReal (1 - ε) ≤ noisyOut A x (f.val x)),
    ⨆ x ∈ f.dom, noisyCost A x

/-- `noisyR(f) = noisyR_{1/3}(f)` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4, p.11: "We define noisyR using worst-input
expected total cost and error at most 1/3"). -/
noncomputable abbrev noisyR {ι : Type} (f : PartialFn ι) : ℝ≥0∞ :=
  noisyReps (1 / 3) f

end Supplement

end NoPerfectRandComp


