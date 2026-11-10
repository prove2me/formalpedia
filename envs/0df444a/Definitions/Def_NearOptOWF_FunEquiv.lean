-- Prove2me | Definitions.Def_NearOptOWF_FunEquiv
-- name    : NearOptOWF_FunEquiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:28.243609+00:00
-- url     : https://prove2.me/theorems/4de00e8e-c292-4046-af77-de026f665f17
-- title:
--   Functionally equivalent circuits
-- statement:
--   Two circuits $C, C'$ with $n$ inputs are **functionally equivalent** if $C(x) = C'(x)$ for every $x \in \{0,1\}^n$.
--
--   This is the relation under which indistinguishability obfuscation hides the circuit, and the relation of Claim 4.7's functional-equivalence clause.
--
--   **Formalization Note** Circuits are the published multi-output circuits `LaconicBarrier.MCircuit`, whose evaluation accepts strings of any length; equivalence is asked on strings of length $n$ only.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4, p.9 (PDF p.11); Claim 4.7, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- Two circuits with `n` inputs are **functionally equivalent**: they give the same output string on
every input `x ∈ {0,1}ⁿ` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.4, p.9 (PDF p.11): "C and iO(C) are functionally
equivalent"; Claim 4.7, p.15 (PDF p.17)).

**Formalization Note** Circuits are the published multi-output circuits `LaconicBarrier.MCircuit`;
`MCircuit.eval` accepts strings of any length, so equivalence is required on strings of length `n`
only. -/
def FunEquiv {n : ℕ} (C C' : MCircuit n) : Prop :=
  ∀ x : List Bool, x.length = n → C.eval x = C'.eval x

end NearOptOWF


