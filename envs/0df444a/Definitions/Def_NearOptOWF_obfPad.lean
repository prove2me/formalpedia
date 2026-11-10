-- Prove2me | Definitions.Def_NearOptOWF_obfPad
-- name    : NearOptOWF_obfPad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:53.300424+00:00
-- url     : https://prove2.me/theorems/6d1106db-24de-43fb-b16f-a8f35938e958
-- title:
--   Obfuscation of a circuit padded to a common size $S$
-- statement:
--   For an obfuscator $i\mathcal O$, a size $S$ and coins $\rho$ of $i\mathcal O$ at size $S$,
--   $$
--   \mathrm{obfPad}_S(C;\rho) = i\mathcal O\bigl(1^\lambda, \mathrm{pad}_S(C); \rho\bigr).
--   $$
--   This is how every obfuscated circuit of the construction is produced ("We will also pad $F$ with sufficiently many dummy gates so that the size of this obfuscated circuit matches other obfuscated circuits later in our proof").
--
--   **Formalization Note** If $|C| > S$ the padded circuit has size $|C|$, not $S$, and the padded circuit itself is returned; every statement of the mission takes $S$ above the sizes it pads.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4, pp.11–12 (PDF pp.13–14)

import Mathlib
import Definitions.Def_NearOptOWF_MIOScheme
import Definitions.Def_NearOptOWF_padTo

namespace NearOptOWF

open LaconicBarrier

/-- The obfuscation of `C` **padded to the common size `S`**, `iO(1^λ, padTo S C; ρ)` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4,
pp.11–12 (PDF pp.13–14): "pad F with sufficiently many dummy gates so that the size of this
obfuscated circuit matches other obfuscated circuits later in our proof"). The coins are those of
`iO` at size `S`.

**Formalization Note** If `|C| > S` the padded circuit has size `|C| ≠ S`, and the padded circuit
itself (unobfuscated) is returned. Every statement of the mission takes `S` above the sizes of the
circuits it pads, so this case never arises there. -/
def obfPad (O : MIOScheme) (lam n S : ℕ) (C : MCircuit n) (ρ : Fin (O.coins lam n S) → Bool) :
    MCircuit n :=
  if h : (padTo S C).size = S then
    O.obf lam n (padTo S C) (fun i => ρ (Fin.cast (congrArg (O.coins lam n) h) i))
  else padTo S C

end NearOptOWF


