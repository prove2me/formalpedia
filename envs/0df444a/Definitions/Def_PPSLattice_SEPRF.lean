-- Prove2me | Definitions.Def_PPSLattice_SEPRF
-- name    : PPSLattice_SEPRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:30.760005+00:00
-- url     : https://prove2.me/theorems/58123092-b873-43c7-8409-5ca8e94787c9
-- title:
--   Somewhere equivocal PRF (SEPRF) scheme: syntax
-- statement:
--   An **SEPRF scheme** for input size $\lambda$ consists of
--
--   1. $\mathrm{Setup}(1^\lambda,1^{\ell_{\mathrm{out}}})\to\mathrm{key}$;
--   2. the deterministic $\mathrm{Eval}(\mathrm{key},x)\to y\in\{0,1\}^{\ell_{\mathrm{out}}}$ for $x\in\{0,1\}^\lambda$;
--   3. $\mathrm{Sim1}(1^\lambda,1^{\ell_{\mathrm{out}}},x^*)\to\mathrm{eqKey}$;
--   4. $\mathrm{Sim2}(\mathrm{eqKey},y^*)\to\mathrm{key}$.
--
--   **Formalization Note** Eval accepts any string as key, since Definition 4.2 applies it to an equivocation key.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, pp.18–19

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A **somewhere equivocal PRF (SEPRF) scheme** for input size `λ`, by the laws of its algorithms:
1. `setup λ ℓ_out`: `Setup(1^λ, 1^{ℓ_out}) → key`;
2. `eval key x`: the deterministic `Eval(key, x) → y ∈ {0,1}^{ℓ_out}`, `x ∈ {0,1}^λ`;
3. `sim1 λ ℓ_out x*`: `Sim1(1^λ, 1^{ℓ_out}, x*) → eqKey`;
4. `sim2 eqKey y*`: `Sim2(eqKey, y*) → key`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, Somewhere Equivocal Pseudorandom Functions, pp.18–19.

**Formalization Note.** Keys and equivocation keys are bit strings; `eval` accepts any string as a
key, since Definition 4.2 applies Eval to an equivocation key ("Eval(key, x) = Eval(eqKey, x)"). -/
structure SEPRF where
  setup : ℕ → ℕ → PMF Str
  eval : Str → Str → Str
  sim1 : ℕ → ℕ → Str → PMF Str
  sim2 : Str → Str → PMF Str

end PPSLattice


